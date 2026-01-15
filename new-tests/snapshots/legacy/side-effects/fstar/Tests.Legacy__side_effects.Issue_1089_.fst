module Tests.Legacy__side_effects.Issue_1089_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let test (x y: Core_models.Option.t_Option i32) : Core_models.Option.t_Option i32 =
  match
    Core_models.Option.impl__map #i32
      #(Core_models.Option.t_Option i32)
      x
      (fun i ->
          let i:i32 = i in
          match y <: Core_models.Option.t_Option i32 with
          | Core_models.Option.Option_Some hoist38 ->
            Core_models.Option.Option_Some (i +! hoist38 <: i32) <: Core_models.Option.t_Option i32
          | Core_models.Option.Option_None  ->
            Core_models.Option.Option_None <: Core_models.Option.t_Option i32)
    <:
    Core_models.Option.t_Option (Core_models.Option.t_Option i32)
  with
  | Core_models.Option.Option_Some some -> some
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option i32
