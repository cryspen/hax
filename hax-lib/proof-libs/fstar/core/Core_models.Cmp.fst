module Core_models.Cmp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

open Rust_primitives.Integers

class t_PartialEq (v_Self: Type0) (v_Rhs: Type0) = {
  f_eq_pre:self_: v_Self -> other: v_Rhs -> pred: Type0{true ==> pred};
  f_eq_post:v_Self -> v_Rhs -> bool -> Type0;
  f_eq:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_eq_pre x0 x1) (fun result -> f_eq_post x0 x1 result)
}

class t_Eq (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_PartialEq v_Self v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Eq v_Self|} -> i._super_i0

type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering

let anon_const_Ordering_Less__anon_const_0: isize = mk_isize (-1)

let anon_const_Ordering_Equal__anon_const_0: isize = mk_isize 0

let anon_const_Ordering_Greater__anon_const_0: isize = mk_isize 1

let t_Ordering_cast_to_repr (x: t_Ordering) : isize =
  match x <: t_Ordering with
  | Ordering_Less  -> anon_const_Ordering_Less__anon_const_0
  | Ordering_Equal  -> anon_const_Ordering_Equal__anon_const_0
  | Ordering_Greater  -> anon_const_Ordering_Greater__anon_const_0

class t_PartialOrd (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_PartialEq v_Self v_Rhs;
  f_partial_cmp_pre:self_: v_Self -> other: v_Rhs -> pred: Type0{true ==> pred};
  f_partial_cmp_post:v_Self -> v_Rhs -> Core_models.Option.t_Option t_Ordering -> Type0;
  f_partial_cmp:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core_models.Option.t_Option t_Ordering)
        (f_partial_cmp_pre x0 x1)
        (fun result -> f_partial_cmp_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Rhs:Type0) {|i: t_PartialOrd v_Self v_Rhs|} -> i._super_i0

class t_Neq (v_Self: Type0) (v_Rhs: Type0) = {
  f_neq_pre:self_: v_Self -> y: v_Rhs -> pred: Type0{true ==> pred};
  f_neq_post:v_Self -> v_Rhs -> bool -> Type0;
  f_neq:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_neq_pre x0 x1) (fun result -> f_neq_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialEq v_T v_T)
    : t_Neq v_T v_T =
  {
    f_neq_pre = (fun (self: v_T) (y: v_T) -> true);
    f_neq_post = (fun (self: v_T) (y: v_T) (out: bool) -> true);
    f_neq
    =
    fun (self: v_T) (y: v_T) ->
      (f_eq #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: bool) =. false
  }

class t_PartialOrdDefaults (v_Self: Type0) (v_Rhs: Type0) = {
  f_lt_pre:{| i0: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_lt_post:{| i0: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_lt:{| i0: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_lt_pre #i0 x0 x1) (fun result -> f_lt_post #i0 x0 x1 result);
  f_le_pre:{| i0: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_le_post:{| i0: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_le:{| i0: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_le_pre #i0 x0 x1) (fun result -> f_le_post #i0 x0 x1 result);
  f_gt_pre:{| i0: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_gt_post:{| i0: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_gt:{| i0: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_gt_pre #i0 x0 x1) (fun result -> f_gt_post #i0 x0 x1 result);
  f_ge_pre:{| i0: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_ge_post:{| i0: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_ge:{| i0: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_ge_pre #i0 x0 x1) (fun result -> f_ge_post #i0 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
    : t_PartialOrdDefaults v_T v_T =
  {
    f_lt_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_lt_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_lt
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y
          <:
          Core_models.Option.t_Option t_Ordering
        with
        | Core_models.Option.Option_Some (Ordering_Less ) -> true
        | _ -> false);
    f_le_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_le_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_le
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y
          <:
          Core_models.Option.t_Option t_Ordering
        with
        | Core_models.Option.Option_Some (Ordering_Less )
        | Core_models.Option.Option_Some (Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_gt_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_gt
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y
          <:
          Core_models.Option.t_Option t_Ordering
        with
        | Core_models.Option.Option_Some (Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_ge_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_ge
    =
    fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T) (self: v_T) (y: v_T) ->
      match
        f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y
        <:
        Core_models.Option.t_Option t_Ordering
      with
      | Core_models.Option.Option_Some (Ordering_Greater )
      | Core_models.Option.Option_Some (Ordering_Equal ) -> true
      | _ -> false
  }

class t_Ord (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Eq v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:t_PartialOrd v_Self v_Self;
  f_cmp_pre:self_: v_Self -> other: v_Self -> pred: Type0{true ==> pred};
  f_cmp_post:v_Self -> v_Self -> t_Ordering -> Type0;
  f_cmp:x0: v_Self -> x1: v_Self
    -> Prims.Pure t_Ordering (f_cmp_pre x0 x1) (fun result -> f_cmp_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Ord v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Ord v_Self|} -> i._super_i1

let max (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T) (v1 v2: v_T) : v_T =
  match f_cmp #v_T #FStar.Tactics.Typeclasses.solve v1 v2 <: t_Ordering with
  | Ordering_Greater  -> v1
  | _ -> v2

let min (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T) (v1 v2: v_T) : v_T =
  match f_cmp #v_T #FStar.Tactics.Typeclasses.solve v1 v2 <: t_Ordering with
  | Ordering_Greater  -> v2
  | _ -> v1

type t_Reverse (v_T: Type0) = | Reverse : v_T -> t_Reverse v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialEq v_T v_T)
    : t_PartialEq (t_Reverse v_T) (t_Reverse v_T) =
  {
    f_eq_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_eq_post = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) (out: bool) -> true);
    f_eq
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_eq #v_T #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
    : t_PartialOrd (t_Reverse v_T) (t_Reverse v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_Reverse v_T)
        (other: t_Reverse v_T)
        (out: Core_models.Option.t_Option t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Eq v_T)
    : t_Eq (t_Reverse v_T) = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T)
    : t_Ord (t_Reverse v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_cmp_post = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) (out: t_Ordering) -> true);
    f_cmp
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_cmp #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_PartialEq u8 u8 =
  {
    f_eq_pre = (fun (self: u8) (other: u8) -> true);
    f_eq_post = (fun (self: u8) (other: u8) (out: bool) -> true);
    f_eq = fun (self: u8) (other: u8) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: t_PartialOrd u8 u8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u8) (other: u8) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u8) (other: u8) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u8) (other: u8) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_u8: t_Eq u8 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_u8: t_Ord u8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u8) (other: u8) -> true);
    f_cmp_post
    =
    (fun (self_: u8) (other: u8) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u8) (other: u8) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: t_PartialEq i8 i8 =
  {
    f_eq_pre = (fun (self: i8) (other: i8) -> true);
    f_eq_post = (fun (self: i8) (other: i8) (out: bool) -> true);
    f_eq = fun (self: i8) (other: i8) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: t_PartialOrd i8 i8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i8) (other: i8) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i8) (other: i8) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i8) (other: i8) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_i8: t_Eq i8 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_i8: t_Ord i8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i8) (other: i8) -> true);
    f_cmp_post
    =
    (fun (self_: i8) (other: i8) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i8) (other: i8) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_PartialEq u16 u16 =
  {
    f_eq_pre = (fun (self: u16) (other: u16) -> true);
    f_eq_post = (fun (self: u16) (other: u16) (out: bool) -> true);
    f_eq = fun (self: u16) (other: u16) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: t_PartialOrd u16 u16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u16) (other: u16) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u16) (other: u16) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u16) (other: u16) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_u16: t_Eq u16 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_u16: t_Ord u16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u16) (other: u16) -> true);
    f_cmp_post
    =
    (fun (self_: u16) (other: u16) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u16) (other: u16) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: t_PartialEq i16 i16 =
  {
    f_eq_pre = (fun (self: i16) (other: i16) -> true);
    f_eq_post = (fun (self: i16) (other: i16) (out: bool) -> true);
    f_eq = fun (self: i16) (other: i16) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: t_PartialOrd i16 i16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i16) (other: i16) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i16) (other: i16) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i16) (other: i16) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_i16: t_Eq i16 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_i16: t_Ord i16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i16) (other: i16) -> true);
    f_cmp_post
    =
    (fun (self_: i16) (other: i16) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i16) (other: i16) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: t_PartialEq u32 u32 =
  {
    f_eq_pre = (fun (self: u32) (other: u32) -> true);
    f_eq_post = (fun (self: u32) (other: u32) (out: bool) -> true);
    f_eq = fun (self: u32) (other: u32) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: t_PartialOrd u32 u32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u32) (other: u32) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u32) (other: u32) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u32) (other: u32) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_u32: t_Eq u32 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_u32: t_Ord u32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u32) (other: u32) -> true);
    f_cmp_post
    =
    (fun (self_: u32) (other: u32) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u32) (other: u32) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: t_PartialEq i32 i32 =
  {
    f_eq_pre = (fun (self: i32) (other: i32) -> true);
    f_eq_post = (fun (self: i32) (other: i32) (out: bool) -> true);
    f_eq = fun (self: i32) (other: i32) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: t_PartialOrd i32 i32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i32) (other: i32) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i32) (other: i32) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i32) (other: i32) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_i32: t_Eq i32 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_i32: t_Ord i32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i32) (other: i32) -> true);
    f_cmp_post
    =
    (fun (self_: i32) (other: i32) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i32) (other: i32) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: t_PartialEq u64 u64 =
  {
    f_eq_pre = (fun (self: u64) (other: u64) -> true);
    f_eq_post = (fun (self: u64) (other: u64) (out: bool) -> true);
    f_eq = fun (self: u64) (other: u64) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: t_PartialOrd u64 u64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u64) (other: u64) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u64) (other: u64) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u64) (other: u64) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_u64: t_Eq u64 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_u64: t_Ord u64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u64) (other: u64) -> true);
    f_cmp_post
    =
    (fun (self_: u64) (other: u64) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u64) (other: u64) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: t_PartialEq i64 i64 =
  {
    f_eq_pre = (fun (self: i64) (other: i64) -> true);
    f_eq_post = (fun (self: i64) (other: i64) (out: bool) -> true);
    f_eq = fun (self: i64) (other: i64) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: t_PartialOrd i64 i64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i64) (other: i64) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i64) (other: i64) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i64) (other: i64) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_i64: t_Eq i64 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_i64: t_Ord i64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i64) (other: i64) -> true);
    f_cmp_post
    =
    (fun (self_: i64) (other: i64) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i64) (other: i64) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: t_PartialEq u128 u128 =
  {
    f_eq_pre = (fun (self: u128) (other: u128) -> true);
    f_eq_post = (fun (self: u128) (other: u128) (out: bool) -> true);
    f_eq = fun (self: u128) (other: u128) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: t_PartialOrd u128 u128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u128) (other: u128) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u128) (other: u128) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u128) (other: u128) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_u128: t_Eq u128 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_u128: t_Ord u128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u128) (other: u128) -> true);
    f_cmp_post
    =
    (fun (self_: u128) (other: u128) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u128) (other: u128) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: t_PartialEq i128 i128 =
  {
    f_eq_pre = (fun (self: i128) (other: i128) -> true);
    f_eq_post = (fun (self: i128) (other: i128) (out: bool) -> true);
    f_eq = fun (self: i128) (other: i128) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: t_PartialOrd i128 i128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i128) (other: i128) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i128) (other: i128) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i128) (other: i128) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_i128: t_Eq i128 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_i128: t_Ord i128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i128) (other: i128) -> true);
    f_cmp_post
    =
    (fun (self_: i128) (other: i128) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i128) (other: i128) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: t_PartialEq usize usize =
  {
    f_eq_pre = (fun (self: usize) (other: usize) -> true);
    f_eq_post = (fun (self: usize) (other: usize) (out: bool) -> true);
    f_eq = fun (self: usize) (other: usize) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: t_PartialOrd usize usize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: usize) (other: usize) -> true);
    f_partial_cmp_post
    =
    (fun (self_: usize) (other: usize) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: usize) (other: usize) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_usize: t_Eq usize = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_usize: t_Ord usize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: usize) (other: usize) -> true);
    f_cmp_post
    =
    (fun (self_: usize) (other: usize) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: usize) (other: usize) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: t_PartialEq isize isize =
  {
    f_eq_pre = (fun (self: isize) (other: isize) -> true);
    f_eq_post = (fun (self: isize) (other: isize) (out: bool) -> true);
    f_eq = fun (self: isize) (other: isize) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: t_PartialOrd isize isize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: isize) (other: isize) -> true);
    f_partial_cmp_post
    =
    (fun (self_: isize) (other: isize) (res: Core_models.Option.t_Option t_Ordering) ->
        match res <: Core_models.Option.t_Option t_Ordering with
        | Core_models.Option.Option_Some (Ordering_Less ) -> self_ <. other
        | Core_models.Option.Option_Some (Ordering_Equal ) -> self_ =. other
        | Core_models.Option.Option_Some (Ordering_Greater ) -> self_ >. other
        | Core_models.Option.Option_None  -> false);
    f_partial_cmp
    =
    fun (self: isize) (other: isize) ->
      Core_models.Option.Option_Some
      (if self <. other
        then Ordering_Less <: t_Ordering
        else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering)
      <:
      Core_models.Option.t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Eq_for_isize: t_Eq isize = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Ord_for_isize: t_Ord isize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: isize) (other: isize) -> true);
    f_cmp_post
    =
    (fun (self_: isize) (other: isize) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: isize) (other: isize) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }
