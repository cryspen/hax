module Core_models.Ops.Arith
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

open Rust_primitives.Integers

class t_AddAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_add_assign_pre:v_Self -> v_Rhs -> Type0;
  f_add_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_add_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_add_assign_pre x0 x1) (fun result -> f_add_assign_post x0 x1 result)
}

class t_SubAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_sub_assign_pre:v_Self -> v_Rhs -> Type0;
  f_sub_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_sub_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_sub_assign_pre x0 x1) (fun result -> f_sub_assign_post x0 x1 result)
}

class t_MulAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_mul_assign_pre:v_Self -> v_Rhs -> Type0;
  f_mul_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_mul_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_mul_assign_pre x0 x1) (fun result -> f_mul_assign_post x0 x1 result)
}

class t_DivAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_div_assign_pre:v_Self -> v_Rhs -> Type0;
  f_div_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_div_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_div_assign_pre x0 x1) (fun result -> f_div_assign_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_AddAssign u8 u8 =
  {
    f_add_assign_pre
    =
    (fun (self_: u8) (rhs: u8) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u8__MAX <: Hax_lib.Int.t_Int));
    f_add_assign_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_add_assign
    =
    fun (self: u8) (rhs: u8) ->
      let self:u8 = self +! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_SubAssign u8 u8 =
  {
    f_sub_assign_pre
    =
    (fun (self_: u8) (rhs: u8) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine (mk_i32 0) <: Hax_lib.Int.t_Int));
    f_sub_assign_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_sub_assign
    =
    fun (self: u8) (rhs: u8) ->
      let self:u8 = self -! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_AddAssign u16 u16 =
  {
    f_add_assign_pre
    =
    (fun (self_: u16) (rhs: u16) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u16__MAX <: Hax_lib.Int.t_Int));
    f_add_assign_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_add_assign
    =
    fun (self: u16) (rhs: u16) ->
      let self:u16 = self +! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: t_SubAssign u16 u16 =
  {
    f_sub_assign_pre
    =
    (fun (self_: u16) (rhs: u16) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine (mk_i32 0) <: Hax_lib.Int.t_Int));
    f_sub_assign_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_sub_assign
    =
    fun (self: u16) (rhs: u16) ->
      let self:u16 = self -! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_AddAssign u32 u32 =
  {
    f_add_assign_pre
    =
    (fun (self_: u32) (rhs: u32) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u32__MAX <: Hax_lib.Int.t_Int));
    f_add_assign_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_add_assign
    =
    fun (self: u32) (rhs: u32) ->
      let self:u32 = self +! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: t_SubAssign u32 u32 =
  {
    f_sub_assign_pre
    =
    (fun (self_: u32) (rhs: u32) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine (mk_i32 0) <: Hax_lib.Int.t_Int));
    f_sub_assign_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_sub_assign
    =
    fun (self: u32) (rhs: u32) ->
      let self:u32 = self -! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_AddAssign u64 u64 =
  {
    f_add_assign_pre
    =
    (fun (self_: u64) (rhs: u64) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u64__MAX <: Hax_lib.Int.t_Int));
    f_add_assign_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_add_assign
    =
    fun (self: u64) (rhs: u64) ->
      let self:u64 = self +! rhs in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_SubAssign u64 u64 =
  {
    f_sub_assign_pre
    =
    (fun (self_: u64) (rhs: u64) ->
        ((Rust_primitives.Hax.Int.from_machine self_ <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine rhs <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine (mk_i32 0) <: Hax_lib.Int.t_Int));
    f_sub_assign_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_sub_assign
    =
    fun (self: u64) (rhs: u64) ->
      let self:u64 = self -! rhs in
      self
  }

class t_Add (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_add_pre:v_Self -> v_Rhs -> Type0;
  f_add_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result)
}

class t_Sub (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_sub_pre:v_Self -> v_Rhs -> Type0;
  f_sub_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result)
}

class t_Mul (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_mul_pre:v_Self -> v_Rhs -> Type0;
  f_mul_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_mul_pre x0 x1) (fun result -> f_mul_post x0 x1 result)
}

class t_Div (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_div_pre:v_Self -> v_Rhs -> Type0;
  f_div_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_div_pre x0 x1) (fun result -> f_div_post x0 x1 result)
}
