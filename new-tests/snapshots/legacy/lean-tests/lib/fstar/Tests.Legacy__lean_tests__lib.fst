module Tests.Legacy__lean_tests__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_FORTYTWO: usize = mk_usize 42

let v_MINUS_FORTYTWO: isize = mk_isize (-42)

let returns42 (_: Prims.unit) : usize = v_FORTYTWO

let add_two_numbers (x y: usize) : usize = x +! y

let letBinding (x y: usize) : usize =
  let useless:Prims.unit = () <: Prims.unit in
  let result1:usize = x +! y in
  let result2:usize = result1 +! mk_usize 2 in
  result2 +! mk_usize 1

let closure (_: Prims.unit) : i32 =
  let x:i32 = mk_i32 41 in
  let f1: i32 -> i32 =
    fun y ->
      let y:i32 = y in
      y +! x
  in
  let f2: i32 -> i32 -> i32 =
    fun y z ->
      let y:i32 = y in
      let z:i32 = z in
      (y +! x <: i32) +! z
  in
  let res1:i32 =
    Core.Ops.Function.f_call #i32 #FStar.Tactics.Typeclasses.solve f1 (mk_i32 1 <: i32)
  in
  let res2:i32 =
    Core.Ops.Function.f_call #(i32 & i32)
      #FStar.Tactics.Typeclasses.solve
      f2
      (mk_i32 2, mk_i32 3 <: (i32 & i32))
  in
  res1 +! res2

(* item error backend: ((Diagnostics.Context.Backend FStar),
 Types.AssertionFailure {
   details =
   "Could not find item with UID (Attr_payloads.UId.T.UId \"0ad959a0909e4c9b940295bdd3fa9bc5\")"})

Last AST:
#[<cfg_attr>(hax_compilation, _hax ::
json("{\"AssociatedItem\":{\"role\":\"ItemQuote\",\"item\":{\"uid\":\"0ad959a0909e4c9b940295bdd3fa9bc5\"}}}"))]#[_hax::json("{\"AssociatedItem\":{\"role\":\"ItemQuote\",\"item\":{\"uid\":\"0ad959a0909e4c9b940295bdd3fa9bc5\"}}}")]#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code)]#[feature(register_tool, if_let_guard)]#[feature(coverage_attribute, stmt_expr_attributes, custom_inner_attributes, test,
yield_expr, coroutines, coroutine_trait, no_core, core_intrinsics)]#[register_tool(_hax)]fn test_before_verbatime_single_line(x: int) -> int{42} *)

(* item error backend: ((Diagnostics.Context.Backend FStar),
 Types.AssertionFailure {
   details =
   "Could not find item with UID (Attr_payloads.UId.T.UId \"a58afa25dee34db7b1a896c83e5e9887\")"})

Last AST:
#[<cfg_attr>(hax_compilation, _hax ::
json("{\"AssociatedItem\":{\"role\":\"ItemQuote\",\"item\":{\"uid\":\"a58afa25dee34db7b1a896c83e5e9887\"}}}"))]#[_hax::json("{\"AssociatedItem\":{\"role\":\"ItemQuote\",\"item\":{\"uid\":\"a58afa25dee34db7b1a896c83e5e9887\"}}}")]#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code)]#[feature(register_tool, if_let_guard)]#[feature(coverage_attribute, stmt_expr_attributes, custom_inner_attributes, test,
yield_expr, coroutines, coroutine_trait, no_core, core_intrinsics)]#[register_tool(_hax)]fn test_before_verbatim_multi_line(x: int) -> int{32} *)

let binop_resugarings (x: u32) : u32 =
  let add:u32 = x +! mk_u32 1 in
  let sub:u32 = add -! mk_u32 2 in
  let mul:u32 = sub *! mk_u32 3 in
  let rem:u32 = mul %! mk_u32 4 in
  let div:u32 = rem /! mk_u32 5 in
  let rshift:u32 = div >>! x in
  x
