module Core_models.Fmt.Rt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

open Rust_primitives.Arrays
open Rust_primitives.Integers

assume
val t_ArgumentType': eqtype

unfold
let t_ArgumentType = t_ArgumentType'

type t_Argument = { f_ty:t_ArgumentType }

assume
val impl__new_display': #v_T: Type0 -> x: v_T -> t_Argument

unfold
let impl__new_display (#v_T: Type0) = impl__new_display' #v_T

assume
val impl__new_debug': #v_T: Type0 -> x: v_T -> t_Argument

unfold
let impl__new_debug (#v_T: Type0) = impl__new_debug' #v_T

assume
val impl__new_lower_hex': #v_T: Type0 -> x: v_T -> t_Argument

unfold
let impl__new_lower_hex (#v_T: Type0) = impl__new_lower_hex' #v_T

assume
val impl_1__new_binary': #v_T: Type0 -> x: v_T -> t_Argument

unfold
let impl_1__new_binary (#v_T: Type0) = impl_1__new_binary' #v_T

assume
val impl_1__new_const': #v_T: Type0 -> #v_U: Type0 -> x: v_T -> y: v_U
  -> Core_models.Fmt.t_Arguments

unfold
let impl_1__new_const (#v_T #v_U: Type0) = impl_1__new_const' #v_T #v_U

assume
val impl_1__new_v1':
    #v_T: Type0 ->
    #v_U: Type0 ->
    #v_V: Type0 ->
    #v_W: Type0 ->
    x: v_T ->
    y: v_U ->
    z: v_V ->
    t: v_W
  -> Core_models.Fmt.t_Arguments

unfold
let impl_1__new_v1 (#v_T #v_U #v_V #v_W: Type0) = impl_1__new_v1' #v_T #v_U #v_V #v_W

let impl_1__none (_: Prims.unit) : t_Array t_Argument (mk_usize 0) =
  let list:Prims.list t_Argument = [] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
  Rust_primitives.Hax.array_of_list 0 list

assume
val impl_1__new_v1_formatted':
    #v_T: Type0 ->
    #v_U: Type0 ->
    #v_V: Type0 ->
    x: v_T ->
    y: v_U ->
    z: v_V
  -> Core_models.Fmt.t_Arguments

unfold
let impl_1__new_v1_formatted (#v_T #v_U #v_V: Type0) = impl_1__new_v1_formatted' #v_T #v_U #v_V

type t_Count =
  | Count_Is : u16 -> t_Count
  | Count_Param : u16 -> t_Count
  | Count_Implied : t_Count

type t_Placeholder = {
  f_position:usize;
  f_flags:u32;
  f_precision:t_Count;
  f_width:t_Count
}

type t_UnsafeArg = | UnsafeArg : t_UnsafeArg
