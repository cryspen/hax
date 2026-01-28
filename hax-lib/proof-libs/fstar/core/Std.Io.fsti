module Std.Io
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Read (v_Self: Type0) = {
  f_read_pre:self_: v_Self -> buf: t_Slice u8 -> pred: Type0{true ==> pred};
  f_read_post:
      self_: v_Self ->
      buf: t_Slice u8 ->
      x: (v_Self & t_Slice u8 & Core_models.Result.t_Result usize Std.Io.Error.t_Error)
    -> pred:
      Type0
        { pred ==>
          (let
            (self_e_future: v_Self),
            (buf_future: t_Slice u8),
            (_: Core_models.Result.t_Result usize Std.Io.Error.t_Error) =
              x
            in
            (Core_models.Slice.impl__len #u8 buf_future <: usize) =.
            (Core_models.Slice.impl__len #u8 buf <: usize)) };
  f_read:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & t_Slice u8 & Core_models.Result.t_Result usize Std.Io.Error.t_Error)
        (f_read_pre x0 x1)
        (fun result -> f_read_post x0 x1 result);
  f_read_exact_pre:self_: v_Self -> buf: t_Slice u8 -> pred: Type0{true ==> pred};
  f_read_exact_post:
      self_: v_Self ->
      buf: t_Slice u8 ->
      x: (v_Self & t_Slice u8 & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
    -> pred:
      Type0
        { pred ==>
          (let
            (self_e_future: v_Self),
            (buf_future: t_Slice u8),
            (_: Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error) =
              x
            in
            (Core_models.Slice.impl__len #u8 buf_future <: usize) =.
            (Core_models.Slice.impl__len #u8 buf <: usize)) };
  f_read_exact:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure
        (v_Self & t_Slice u8 & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        (f_read_exact_pre x0 x1)
        (fun result -> f_read_exact_post x0 x1 result)
}

class t_Write (v_Self: Type0) = {
  f_write_pre:self_: v_Self -> buf: t_Slice u8 -> pred: Type0{true ==> pred};
  f_write_post:
      v_Self ->
      t_Slice u8 ->
      (v_Self & Core_models.Result.t_Result usize Std.Io.Error.t_Error)
    -> Type0;
  f_write:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & Core_models.Result.t_Result usize Std.Io.Error.t_Error)
        (f_write_pre x0 x1)
        (fun result -> f_write_post x0 x1 result);
  f_flush_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_flush_post:v_Self -> (v_Self & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
    -> Type0;
  f_flush:x0: v_Self
    -> Prims.Pure (v_Self & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        (f_flush_pre x0)
        (fun result -> f_flush_post x0 result);
  f_write_all_pre:self_: v_Self -> buf: t_Slice u8 -> pred: Type0{true ==> pred};
  f_write_all_post:
      v_Self ->
      t_Slice u8 ->
      (v_Self & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
    -> Type0;
  f_write_all:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & Core_models.Result.t_Result Prims.unit Std.Io.Error.t_Error)
        (f_write_all_pre x0 x1)
        (fun result -> f_write_all_post x0 x1 result)
}
