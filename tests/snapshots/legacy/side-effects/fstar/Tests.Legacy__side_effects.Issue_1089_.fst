module Tests.Legacy__side_effects.Issue_1089_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let test (x y: Core.Option.t_Option i32) : Core.Option.t_Option i32 =
  match
    Core.Option.impl__map #i32
      #(Core.Option.t_Option i32)
      x
      (fun i ->
          let i:i32 = i in
          match y <: Core.Option.t_Option i32 with
          | Core.Option.Option_Some hoist38 ->
            Core.Option.Option_Some (i +! hoist38 <: i32) <: Core.Option.t_Option i32
          | Core.Option.Option_None  -> Core.Option.Option_None <: Core.Option.t_Option i32)
    <:
    Core.Option.t_Option (Core.Option.t_Option i32)
  with
  | Core.Option.Option_Some some -> some
  | Core.Option.Option_None  -> Core.Option.Option_None <: Core.Option.t_Option i32
