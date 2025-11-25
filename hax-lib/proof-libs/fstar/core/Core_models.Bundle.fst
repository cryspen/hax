module Core_models.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Option (v_T: Type0) =
  | Option_Some : v_T -> t_Option v_T
  | Option_None : t_Option v_T

let impl__is_some_and
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Option v_T)
      (f: v_F)
    : bool =
  match self <: t_Option v_T with
  | Option_None  -> false
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f x

let impl__is_none_or
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Option v_T)
      (f: v_F)
    : bool =
  match self <: t_Option v_T with
  | Option_None  -> true
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f x

let impl__as_ref (#v_T: Type0) (self: t_Option v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

let impl__unwrap_or (#v_T: Type0) (self: t_Option v_T) (v_default: v_T) : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> v_default

let impl__unwrap_or_else
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_Option v_T)
      (f: v_F)
    : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  ->
    Core_models.Ops.Function.f_call_once #v_F
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      f
      (() <: Prims.unit)

let impl__unwrap_or_default
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Option v_T)
    : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

let impl__map
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_U =
  match self <: t_Option v_T with
  | Option_Some x ->
    Option_Some
    (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f x)
    <:
    t_Option v_U
  | Option_None  -> Option_None <: t_Option v_U

let impl__map_or
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (v_default: v_U)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Option_None  -> v_default

let impl__map_or_else
      (#v_T #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_D Prims.unit)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (v_default: v_D)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Option_None  ->
    Core_models.Ops.Function.f_call_once #v_D
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      v_default
      (() <: Prims.unit)

let impl__map_or_default
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_U)
      (self: t_Option v_T)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Option_None  -> Core_models.Default.f_default #v_U #FStar.Tactics.Typeclasses.solve ()

let impl__and_then
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Option v_U})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_U =
  match self <: t_Option v_T with
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f x
  | Option_None  -> Option_None <: t_Option v_U

let impl__take (#v_T: Type0) (self: t_Option v_T) : (t_Option v_T & t_Option v_T) =
  (Option_None <: t_Option v_T), self <: (t_Option v_T & t_Option v_T)

let impl__is_some (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun res ->
          let res:bool = res in
          b2t res ==> Option_Some? self) =
  match self <: t_Option v_T with
  | Option_Some _ -> true
  | _ -> false

let impl__is_none (#v_T: Type0) (self: t_Option v_T) : bool =
  (impl__is_some #v_T self <: bool) =. false

let impl__expect (#v_T: Type0) (self: t_Option v_T) (e_msg: string)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

let impl__unwrap (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

type t_Result (v_T: Type0) (v_E: Type0) =
  | Result_Ok : v_T -> t_Result v_T v_E
  | Result_Err : v_E -> t_Result v_T v_E

let impl__ok_or (#v_T #v_E: Type0) (self: t_Option v_T) (err: v_E) : t_Result v_T v_E =
  match self <: t_Option v_T with
  | Option_Some v -> Result_Ok v <: t_Result v_T v_E
  | Option_None  -> Result_Err err <: t_Result v_T v_E

let impl__ok_or_else
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_E})
      (self: t_Option v_T)
      (err: v_F)
    : t_Result v_T v_E =
  match self <: t_Option v_T with
  | Option_Some v -> Result_Ok v <: t_Result v_T v_E
  | Option_None  ->
    Result_Err
    (Core_models.Ops.Function.f_call_once #v_F
        #Prims.unit
        #FStar.Tactics.Typeclasses.solve
        err
        (() <: Prims.unit))
    <:
    t_Result v_T v_E

let impl__map__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (op: v_F)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Result_Ok (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve op t)
    <:
    t_Result v_U v_E
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

let impl__map_or__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (v_default: v_U)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Result_Err e_e -> v_default

let impl__map_or_else__from__result
      (#v_T #v_E #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_FnOnce v_D v_E)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (v_default: v_D)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_D #v_E #FStar.Tactics.Typeclasses.solve v_default e

let impl__map_err
      (#v_T #v_E #v_F #v_O: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_O v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_F})
      (self: t_Result v_T v_E)
      (op: v_O)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err e ->
    Result_Err
    (Core_models.Ops.Function.f_call_once #v_O #v_E #FStar.Tactics.Typeclasses.solve op e)
    <:
    t_Result v_T v_F

let impl__is_ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> true
  | _ -> false

let impl__and_then__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_U v_E})
      (self: t_Result v_T v_E)
      (op: v_F)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve op t
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

let impl__ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Option v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok x -> Option_Some x <: t_Option v_T
  | Result_Err _ -> Option_None <: t_Option v_T

let impl__unwrap__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_T (requires impl__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

let impl__expect__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_T (requires impl__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()
