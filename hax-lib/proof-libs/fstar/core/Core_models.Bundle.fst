module Core_models.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::option::Option`]
type t_Option (v_T: Type0) =
  | Option_Some : v_T -> t_Option v_T
  | Option_None : t_Option v_T

/// See [`std::option::Option::is_some_and`]
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

/// See [`std::option::Option::is_none_or`]
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

/// See [`std::option::Option::as_ref`]
let impl__as_ref (#v_T: Type0) (self: t_Option v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Option::unwrap_or`]
let impl__unwrap_or (#v_T: Type0) (self: t_Option v_T) (v_default: v_T) : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> v_default

/// See [`std::option::Option::unwrap_or_else`]
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

/// See [`std::option::Option::unwrap_or_default`]
let impl__unwrap_or_default
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Option v_T)
    : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::option::Option::map`]
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

/// See [`std::option::Option::map_or`]
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

/// See [`std::option::Option::map_or_else`]
let impl__map_or_else
      (#v_T #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_D Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
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

/// See [`std::option::Option::map_or_default`]
let impl__map_or_default
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_U)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Option_None  -> Core_models.Default.f_default #v_U #FStar.Tactics.Typeclasses.solve ()

/// See [`std::option::Option::and_then`]
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

/// See [`std::option::Option::take`]
/// Note: The interface in Rust is wrong, but is good after extraction.
/// We cannot make a useful model with the right interface so we lose the executability.
let impl__take (#v_T: Type0) (self: t_Option v_T) : (t_Option v_T & t_Option v_T) =
  (Option_None <: t_Option v_T), self <: (t_Option v_T & t_Option v_T)

/// See [`std::option::Option::is_some`]
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

/// See [`std::option::Option::is_none`]
let impl__is_none (#v_T: Type0) (self: t_Option v_T) : bool =
  (impl__is_some #v_T self <: bool) =. false

/// See [`std::option::Option::expect`]
let impl__expect (#v_T: Type0) (self: t_Option v_T) (e_msg: string)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::option::Option::unwrap`]
let impl__unwrap (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result`]
type t_Result (v_T: Type0) (v_E: Type0) =
  | Result_Ok : v_T -> t_Result v_T v_E
  | Result_Err : v_E -> t_Result v_T v_E

/// See [`std::option::Option::ok_or`]
let impl__ok_or (#v_T #v_E: Type0) (self: t_Option v_T) (err: v_E) : t_Result v_T v_E =
  match self <: t_Option v_T with
  | Option_Some v -> Result_Ok v <: t_Result v_T v_E
  | Option_None  -> Result_Err err <: t_Result v_T v_E

/// See [`std::option::Option::ok_or_else`]
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

/// See [`std::result::Result::is_ok`]
let impl_3__is_ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> true
  | _ -> false

/// See [`std::result::Result::is_ok_and`]
let impl_3__is_ok_and
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Result v_T v_E)
      (f: v_F)
    : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Result_Err _ -> false

/// See [`std::result::Result::is_err`]
let impl_3__is_err (#v_T #v_E: Type0) (self: t_Result v_T v_E) : bool =
  ~.(impl_3__is_ok #v_T #v_E self <: bool)

/// See [`std::result::Result::is_err_and`]
let impl_3__is_err_and
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Result v_T v_E)
      (f: v_F)
    : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> false
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve f e

/// See [`std::result::Result::as_ref`]
let impl_3__as_ref (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::unwrap_or`]
let impl_3__unwrap_or (#v_T #v_E: Type0) (self: t_Result v_T v_E) (v_default: v_T) : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> v_default

/// See [`std::result::Result::unwrap_or_else`]
let impl_3__unwrap_or_else
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_Result v_T v_E)
      (op: v_F)
    : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve op e

/// See [`std::result::Result::unwrap_or_default`]
let impl_3__unwrap_or_default
      (#v_T #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Result v_T v_E)
    : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::result::Result::map`]
let impl_3__map
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

/// See [`std::result::Result::map_or`]
let impl_3__map_or
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
  | Result_Err _ -> v_default

/// See [`std::result::Result::map_or_else`]
let impl_3__map_or_else
      (#v_T #v_E #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_FnOnce v_D v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
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

/// See [`std::result::Result::map_or_default`]
let impl_3__map_or_default
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_U)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
  | Result_Err _ -> Core_models.Default.f_default #v_U #FStar.Tactics.Typeclasses.solve ()

/// See [`std::result::Result::map_err`]
let impl_3__map_err
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

/// See [`std::result::Result::inspect`]
let impl_3__inspect
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (self: t_Result v_T v_E)
      (f: v_F)
    : t_Result v_T v_E =
  let _:Prims.unit =
    match self <: t_Result v_T v_E with
    | Result_Ok t ->
      let _:Prims.unit =
        Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f t
      in
      ()
    | _ -> ()
  in
  self

/// See [`std::result::Result::inspect_err`]
let impl_3__inspect_err
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (self: t_Result v_T v_E)
      (f: v_F)
    : t_Result v_T v_E =
  let _:Prims.unit =
    match self <: t_Result v_T v_E with
    | Result_Err e ->
      let _:Prims.unit =
        Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve f e
      in
      ()
    | _ -> ()
  in
  self

/// See [`std::result::Result::ok`]
let impl_3__ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Option v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok x -> Option_Some x <: t_Option v_T
  | Result_Err _ -> Option_None <: t_Option v_T

/// See [`std::result::Result::err`]
let impl_3__err (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Option v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Option_None <: t_Option v_E
  | Result_Err e -> Option_Some e <: t_Option v_E

/// See [`std::result::Result::and`]
let impl_3__and (#v_T #v_E #v_U: Type0) (self: t_Result v_T v_E) (res: t_Result v_U v_E)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> res
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

/// See [`std::result::Result::and_then`]
let impl_3__and_then
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

/// See [`std::result::Result::or`]
let impl_3__or (#v_T #v_E #v_F: Type0) (self: t_Result v_T v_E) (res: t_Result v_T v_F)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err _ -> res

/// See [`std::result::Result::or_else`]
let impl_3__or_else
      (#v_T #v_E #v_F #v_O: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_O v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_T v_F})
      (self: t_Result v_T v_E)
      (op: v_O)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_O #v_E #FStar.Tactics.Typeclasses.solve op e

/// See [`std::result::Result::expect`]
let impl_3__expect (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_T (requires impl_3__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::unwrap`]
let impl_3__unwrap (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_T (requires impl_3__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::expect_err`]
let impl_3__expect_err (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_E (requires impl_3__is_err #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::result::Result::unwrap_err`]
let impl_3__unwrap_err (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_E (requires impl_3__is_err #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::result::Result::cloned`]
let impl__cloned
      (#v_T #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_Result v_T v_E)
    : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Result_Ok (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve t)
    <:
    t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::transpose`]
let impl_1__transpose (#v_T #v_E: Type0) (self: t_Result (t_Option v_T) v_E)
    : t_Option (t_Result v_T v_E) =
  match self <: t_Result (t_Option v_T) v_E with
  | Result_Ok (Option_Some t) ->
    Option_Some (Result_Ok t <: t_Result v_T v_E) <: t_Option (t_Result v_T v_E)
  | Result_Ok (Option_None ) -> Option_None <: t_Option (t_Result v_T v_E)
  | Result_Err e -> Option_Some (Result_Err e <: t_Result v_T v_E) <: t_Option (t_Result v_T v_E)

/// See [`std::result::Result::flatten`]
let impl_2__flatten (#v_T #v_E: Type0) (self: t_Result (t_Result v_T v_E) v_E) : t_Result v_T v_E =
  match self <: t_Result (t_Result v_T v_E) v_E with
  | Result_Ok inner -> inner
  | Result_Err e -> Result_Err e <: t_Result v_T v_E
