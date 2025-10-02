
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Tests.Rustc_tests__inline.length
  (T : Type) (xs : (RustSlice T))
  : Result usize
  := do
  (← Core.Slice.Impl.len T xs)

def Tests.Rustc_tests__inline.swap
  (T : Type) [(Core.Marker.Copy T)] (xs : (RustSlice T))
  (i : usize)
  (j : usize)
  : Result (RustSlice T)
  := do
  let t : T ← (pure (← Core.Ops.Index.Index.index xs i));
  let xs : (RustSlice T) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        xs
        i
        (← Core.Ops.Index.Index.index xs j)));
  let xs : (RustSlice T) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize xs j t));
  xs

def Tests.Rustc_tests__inline.display
  (T : Type) [(Core.Fmt.Display T)] (xs : (RustSlice T))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Rust_primitives.Hax.failure
        "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
        "{
 for x in (core::iter::traits::collect::f_into_iter(xs)) {
 {
 let args: [core::fmt::rt::t_Argument; 1] = {
 [core::fmt::rt::impl__new_display::<T>(x)]
 };
 {
 let _: tuple0 = {
 std::io::stdio::e_p..."));
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__inline.error
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.never_to_any
      (← Core.Panicking.panic_fmt
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["error"])))

def Tests.Rustc_tests__inline.permutate
  (T : Type) [(Core.Marker.Copy T)] [(Core.Fmt.Display T)] (xs : (RustSlice T))
  (k : usize)
  : Result (RustSlice T)
  := do
  let n : usize ← (pure (← Tests.Rustc_tests__inline.length T xs));
  let xs : (RustSlice T) ← (pure
    (← if (← Rust_primitives.Hax.Machine_int.eq k n) then do
      let _ ← (pure (← Tests.Rustc_tests__inline.display T xs));
      xs
    else do
      (← if (← Rust_primitives.Hax.Machine_int.lt k n) then do
        (← Rust_primitives.Hax.Folds.fold_range
            k
            n
            (fun xs _ => (do true : Result Bool))
            xs
            (fun xs i => (do
                let xs : (RustSlice T) ← (pure
                  (← Tests.Rustc_tests__inline.swap T xs i k));
                let xs : (RustSlice T) ← (pure
                  (← Tests.Rustc_tests__inline.permutate T
                      xs
                      (← k +? (1 : usize))));
                let xs : (RustSlice T) ← (pure
                  (← Tests.Rustc_tests__inline.swap T xs i k));
                xs : Result (RustSlice T))))
      else do
        let _ ← (pure
          (← Tests.Rustc_tests__inline.error Rust_primitives.Hax.Tuple0.mk));
        xs)));
  xs

def Tests.Rustc_tests__inline.permutations
  (T : Type) [(Core.Marker.Copy T)] [(Core.Fmt.Display T)] (xs : (RustSlice T))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let ys : (Alloc.Vec.Vec T Alloc.Alloc.Global) ← (pure
    (← Alloc.Borrow.ToOwned.to_owned xs));
  let ys : (Alloc.Vec.Vec T Alloc.Alloc.Global) ← (pure
    (← Tests.Rustc_tests__inline.permutate T ys (0 : usize)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__inline.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__inline.permutations Char
        (← Rust_primitives.unsize #v['a', 'b', 'c'])));
  Rust_primitives.Hax.Tuple0.mk