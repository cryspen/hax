module Core_models.Panicking.Panic_const
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

///`core::panicking::panic_const::panic_const_add_overflow`; std\'s message is \"attempt to add with overflow\".
assume
val panic_const_add_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_add_overflow = panic_const_add_overflow'

///`core::panicking::panic_const::panic_const_sub_overflow`; std\'s message is \"attempt to subtract with overflow\".
assume
val panic_const_sub_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_sub_overflow = panic_const_sub_overflow'

///`core::panicking::panic_const::panic_const_mul_overflow`; std\'s message is \"attempt to multiply with overflow\".
assume
val panic_const_mul_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_mul_overflow = panic_const_mul_overflow'

///`core::panicking::panic_const::panic_const_div_overflow`; std\'s message is \"attempt to divide with overflow\".
assume
val panic_const_div_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_div_overflow = panic_const_div_overflow'

///`core::panicking::panic_const::panic_const_rem_overflow`; std\'s message is \"attempt to calculate the remainder with overflow\".
assume
val panic_const_rem_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_rem_overflow = panic_const_rem_overflow'

///`core::panicking::panic_const::panic_const_neg_overflow`; std\'s message is \"attempt to negate with overflow\".
assume
val panic_const_neg_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_neg_overflow = panic_const_neg_overflow'

///`core::panicking::panic_const::panic_const_shr_overflow`; std\'s message is \"attempt to shift right with overflow\".
assume
val panic_const_shr_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_shr_overflow = panic_const_shr_overflow'

///`core::panicking::panic_const::panic_const_shl_overflow`; std\'s message is \"attempt to shift left with overflow\".
assume
val panic_const_shl_overflow': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_shl_overflow = panic_const_shl_overflow'

///`core::panicking::panic_const::panic_const_div_by_zero`; std\'s message is \"attempt to divide by zero\".
assume
val panic_const_div_by_zero': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_div_by_zero = panic_const_div_by_zero'

///`core::panicking::panic_const::panic_const_rem_by_zero`; std\'s message is \"attempt to calculate the remainder with a divisor of zero\".
assume
val panic_const_rem_by_zero': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_rem_by_zero = panic_const_rem_by_zero'

///`core::panicking::panic_const::panic_const_coroutine_resumed`; std\'s message is \"coroutine resumed after completion\".
assume
val panic_const_coroutine_resumed': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_coroutine_resumed = panic_const_coroutine_resumed'

///`core::panicking::panic_const::panic_const_async_fn_resumed`; std\'s message is \"`async fn` resumed after completion\".
assume
val panic_const_async_fn_resumed': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_fn_resumed = panic_const_async_fn_resumed'

///`core::panicking::panic_const::panic_const_async_gen_fn_resumed`; std\'s message is \"`async gen fn` resumed after completion\".
assume
val panic_const_async_gen_fn_resumed': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_gen_fn_resumed = panic_const_async_gen_fn_resumed'

///`core::panicking::panic_const::panic_const_gen_fn_none`; std\'s message is \"`gen fn` should just keep returning `None` after completion\".
assume
val panic_const_gen_fn_none': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_gen_fn_none = panic_const_gen_fn_none'

///`core::panicking::panic_const::panic_const_coroutine_resumed_panic`; std\'s message is \"coroutine resumed after panicking\".
assume
val panic_const_coroutine_resumed_panic': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_coroutine_resumed_panic = panic_const_coroutine_resumed_panic'

///`core::panicking::panic_const::panic_const_async_fn_resumed_panic`; std\'s message is \"`async fn` resumed after panicking\".
assume
val panic_const_async_fn_resumed_panic': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_fn_resumed_panic = panic_const_async_fn_resumed_panic'

///`core::panicking::panic_const::panic_const_async_gen_fn_resumed_panic`; std\'s message is \"`async gen fn` resumed after panicking\".
assume
val panic_const_async_gen_fn_resumed_panic': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_gen_fn_resumed_panic = panic_const_async_gen_fn_resumed_panic'

///`core::panicking::panic_const::panic_const_gen_fn_none_panic`; std\'s message is \"`gen fn` should just keep returning `None` after panicking\".
assume
val panic_const_gen_fn_none_panic': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_gen_fn_none_panic = panic_const_gen_fn_none_panic'

///`core::panicking::panic_const::panic_const_coroutine_resumed_drop`; std\'s message is \"coroutine resumed after async drop\".
assume
val panic_const_coroutine_resumed_drop': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_coroutine_resumed_drop = panic_const_coroutine_resumed_drop'

///`core::panicking::panic_const::panic_const_async_fn_resumed_drop`; std\'s message is \"`async fn` resumed after async drop\".
assume
val panic_const_async_fn_resumed_drop': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_fn_resumed_drop = panic_const_async_fn_resumed_drop'

///`core::panicking::panic_const::panic_const_async_gen_fn_resumed_drop`; std\'s message is \"`async gen fn` resumed after async drop\".
assume
val panic_const_async_gen_fn_resumed_drop': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_async_gen_fn_resumed_drop = panic_const_async_gen_fn_resumed_drop'

///`core::panicking::panic_const::panic_const_gen_fn_none_drop`; std\'s message is \"`gen fn` resumed after async drop\".
assume
val panic_const_gen_fn_none_drop': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_const_gen_fn_none_drop = panic_const_gen_fn_none_drop'
