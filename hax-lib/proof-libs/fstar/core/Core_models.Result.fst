module Core_models.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

type t_Result (v_T: Type0) (v_E: Type0) =
  | Result_Ok : v_T -> t_Result v_T v_E
  | Result_Err : v_E -> t_Result v_T v_E

let impl__map
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

let impl__map_or
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
  | Result_Err e -> v_default

let impl__map_or_else
      (#v_T #v_E #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_U})
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_FnOnce v_D v_E)
      (#_: unit{i2.Core_models.Ops.Function.f_Output == v_U})
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
      (#v_T #v_E #v_O #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core_models.Ops.Function.t_FnOnce v_O v_E)
      (#_: unit{i3.Core_models.Ops.Function.f_Output == v_F})
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

let impl__and_then
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

let impl__unwrap (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_T (requires Result_Ok? self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

let impl__expect (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_T (requires Result_Ok? self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

let impl__is_ok (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun res ->
          let res:bool = res in
          b2t res ==> Result_Ok? self) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> true
  | _ -> false
