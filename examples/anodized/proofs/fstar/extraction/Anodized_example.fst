module Anodized_example
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let f1 (x: u8) : Prims.Pure Prims.unit (requires x >. mk_u8 0) (fun _ -> Prims.l_True) = ()

/// Reference for comparison
let f2 (x: u8) : Prims.Pure Prims.unit (requires x >. mk_u8 0) (fun _ -> Prims.l_True) = ()

let f3 (x: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun output ->
          let output:u8 = output in
          output =. x) = x

let f4 (x: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun res ->
          let res:u8 = res in
          res =. x) = x

/// Reference for comparison. `hax_lib::ensures` binds the result by value,
/// where `anodized` binds it by reference.
let f5 (x: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun res ->
          let res:u8 = res in
          res =. x) = x

let f6 (x: u8)
    : Prims.Pure u8
      (requires x >. mk_u8 0)
      (ensures
        fun x_future ->
          let x_future:u8 = x_future in
          x >. mk_u8 0) = x
