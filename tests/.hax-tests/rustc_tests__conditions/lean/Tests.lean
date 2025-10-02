
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

def Tests.Rustc_tests__conditions.main.B : u32 := 100

def Tests.Rustc_tests__conditions.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let countdown : u32 ← (pure (0 : u32));
  let countdown : u32 ← (pure
    (← if true then do
      let countdown : u32 ← (pure (10 : u32));
      countdown
    else do
      countdown));
  (← if (← Rust_primitives.Hax.Machine_int.gt countdown (7 : u32)) then do
    let countdown : u32 ← (pure (← countdown -? (4 : u32)));
    let ⟨countdown, x⟩ ← (pure
      (Rust_primitives.Hax.Tuple2.mk
        countdown Tests.Rustc_tests__conditions.main.B));
    let countdown : i32 ← (pure (0 : i32));
    let countdown : i32 ← (pure
      (← if true then do
        let countdown : i32 ← (pure (10 : i32));
        countdown
      else do
        countdown));
    (← if (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
      let countdown : i32 ← (pure (← countdown -? (4 : i32)));
      (← if true then do
        let countdown : i32 ← (pure (0 : i32));
        let countdown : i32 ← (pure
          (← if true then do
            let countdown : i32 ← (pure (10 : i32));
            countdown
          else do
            countdown));
        (← if (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
          let countdown : i32 ← (pure (← countdown -? (4 : i32)));
          let countdown : i32 ← (pure (0 : i32));
          let countdown : i32 ← (pure
            (← if true then do
              let countdown : i32 ← (pure (1 : i32));
              countdown
            else do
              countdown));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let ⟨countdown, z⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk
                countdown Rust_primitives.Hax.Tuple0.mk));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, w⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk))
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              let should_be_reachable : i32 ← (pure countdown);
              let _ ← (pure
                (← Std.Io.Stdio._print
                    (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                        #v["reached
"])));
              let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
              Rust_primitives.Hax.Tuple0.mk))
        else do
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
            let countdown : i32 ← (pure
              (← if
              (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                  ||? (← Rust_primitives.Hax.Machine_int.gt
                      countdown
                      (5 : i32)))
                ||? (← Rust_primitives.Hax.Machine_int.ne countdown (9 : i32)))
              then do
                let countdown : i32 ← (pure (0 : i32));
                countdown
              else do
                countdown));
            let countdown : i32 ← (pure (← countdown -? (5 : i32)));
            let countdown : i32 ← (pure (0 : i32));
            let countdown : i32 ← (pure
              (← if true then do
                let countdown : i32 ← (pure (1 : i32));
                countdown
              else do
                countdown));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                let should_be_reachable : i32 ← (pure countdown);
                let _ ← (pure
                  (← Std.Io.Stdio._print
                      (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                          #v["reached
"])));
                let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                Rust_primitives.Hax.Tuple0.mk))
          else do
            Rust_primitives.Hax.Tuple0.mk))
      else do
        let countdown : i32 ← (pure (0 : i32));
        let countdown : i32 ← (pure
          (← if true then do
            let countdown : i32 ← (pure (1 : i32));
            countdown
          else do
            countdown));
        (← if (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
          let countdown : i32 ← (pure (← countdown -? (4 : i32)));
          let ⟨countdown, z⟩ ← (pure
            (Rust_primitives.Hax.Tuple2.mk
              countdown Rust_primitives.Hax.Tuple0.mk));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let ⟨countdown, w⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk
                countdown Rust_primitives.Hax.Tuple0.mk));
            Rust_primitives.Hax.Tuple0.mk
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let ⟨countdown, w⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk
            else do
              Rust_primitives.Hax.Tuple0.mk))
        else do
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
            let countdown : i32 ← (pure
              (← if
              (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                  ||? (← Rust_primitives.Hax.Machine_int.gt
                      countdown
                      (5 : i32)))
                ||? (← Rust_primitives.Hax.Machine_int.ne countdown (9 : i32)))
              then do
                let countdown : i32 ← (pure (0 : i32));
                countdown
              else do
                countdown));
            let countdown : i32 ← (pure (← countdown -? (5 : i32)));
            let ⟨countdown, z⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk
                countdown Rust_primitives.Hax.Tuple0.mk));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, w⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk))
          else do
            let should_be_reachable : i32 ← (pure countdown);
            let _ ← (pure
              (← Std.Io.Stdio._print
                  (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["reached
"])));
            let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
            Rust_primitives.Hax.Tuple0.mk)))
    else do
      (← if (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
        let countdown : i32 ← (pure
          (← if
          (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
              ||? (← Rust_primitives.Hax.Machine_int.gt countdown (5 : i32)))
            ||? (← Rust_primitives.Hax.Machine_int.ne countdown (9 : i32))) then
          do
            let countdown : i32 ← (pure (0 : i32));
            countdown
          else do
            countdown));
        let countdown : i32 ← (pure (← countdown -? (5 : i32)));
        (← if true then do
          let countdown : i32 ← (pure (0 : i32));
          let countdown : i32 ← (pure
            (← if true then do
              let countdown : i32 ← (pure (10 : i32));
              countdown
            else do
              countdown));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let countdown : i32 ← (pure (0 : i32));
            let countdown : i32 ← (pure
              (← if true then do
                let countdown : i32 ← (pure (1 : i32));
                countdown
              else do
                countdown));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                let should_be_reachable : i32 ← (pure countdown);
                let _ ← (pure
                  (← Std.Io.Stdio._print
                      (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                          #v["reached
"])));
                let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                Rust_primitives.Hax.Tuple0.mk))
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let countdown : i32 ← (pure (0 : i32));
              let countdown : i32 ← (pure
                (← if true then do
                  let countdown : i32 ← (pure (1 : i32));
                  countdown
                else do
                  countdown));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, z⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32))
                  then do
                    let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    (← if
                    (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                    then do
                      let countdown : i32 ← (pure
                        (← if
                        (← (← (← Rust_primitives.Hax.Machine_int.lt
                                countdown
                                (1 : i32))
                            ||? (← Rust_primitives.Hax.Machine_int.gt
                                countdown
                                (5 : i32)))
                          ||? (← Rust_primitives.Hax.Machine_int.ne
                              countdown
                              (9 : i32))) then do
                          let countdown : i32 ← (pure (0 : i32));
                          countdown
                        else do
                          countdown));
                      let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                      let ⟨countdown, w⟩ ← (pure
                        (Rust_primitives.Hax.Tuple2.mk
                          countdown Rust_primitives.Hax.Tuple0.mk));
                      Rust_primitives.Hax.Tuple0.mk
                    else do
                      Rust_primitives.Hax.Tuple0.mk))
                else do
                  let should_be_reachable : i32 ← (pure countdown);
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["reached
"])));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              Rust_primitives.Hax.Tuple0.mk))
        else do
          let countdown : i32 ← (pure (0 : i32));
          let countdown : i32 ← (pure
            (← if true then do
              let countdown : i32 ← (pure (1 : i32));
              countdown
            else do
              countdown));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let ⟨countdown, z⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk
                countdown Rust_primitives.Hax.Tuple0.mk));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, w⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk))
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              let should_be_reachable : i32 ← (pure countdown);
              let _ ← (pure
                (← Std.Io.Stdio._print
                    (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                        #v["reached
"])));
              let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
              Rust_primitives.Hax.Tuple0.mk)))
      else do
        Rust_primitives.Hax.Tuple0.mk))
  else do
    (← if (← Rust_primitives.Hax.Machine_int.gt countdown (2 : u32)) then do
      let countdown : u32 ← (pure
        (← if
        (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : u32))
            ||? (← Rust_primitives.Hax.Machine_int.gt countdown (5 : u32)))
          ||? (← Rust_primitives.Hax.Machine_int.ne countdown (9 : u32))) then
        do
          let countdown : u32 ← (pure (0 : u32));
          countdown
        else do
          countdown));
      let countdown : u32 ← (pure (← countdown -? (5 : u32)));
      let ⟨countdown, x⟩ ← (pure
        (Rust_primitives.Hax.Tuple2.mk countdown countdown));
      let countdown : i32 ← (pure (0 : i32));
      let countdown : i32 ← (pure
        (← if true then do
          let countdown : i32 ← (pure (10 : i32));
          countdown
        else do
          countdown));
      (← if (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
        let countdown : i32 ← (pure (← countdown -? (4 : i32)));
        (← if true then do
          let countdown : i32 ← (pure (0 : i32));
          let countdown : i32 ← (pure
            (← if true then do
              let countdown : i32 ← (pure (10 : i32));
              countdown
            else do
              countdown));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let countdown : i32 ← (pure (0 : i32));
            let countdown : i32 ← (pure
              (← if true then do
                let countdown : i32 ← (pure (1 : i32));
                countdown
              else do
                countdown));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                let should_be_reachable : i32 ← (pure countdown);
                let _ ← (pure
                  (← Std.Io.Stdio._print
                      (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                          #v["reached
"])));
                let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                Rust_primitives.Hax.Tuple0.mk))
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let countdown : i32 ← (pure (0 : i32));
              let countdown : i32 ← (pure
                (← if true then do
                  let countdown : i32 ← (pure (1 : i32));
                  countdown
                else do
                  countdown));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, z⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32))
                  then do
                    let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    (← if
                    (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                    then do
                      let countdown : i32 ← (pure
                        (← if
                        (← (← (← Rust_primitives.Hax.Machine_int.lt
                                countdown
                                (1 : i32))
                            ||? (← Rust_primitives.Hax.Machine_int.gt
                                countdown
                                (5 : i32)))
                          ||? (← Rust_primitives.Hax.Machine_int.ne
                              countdown
                              (9 : i32))) then do
                          let countdown : i32 ← (pure (0 : i32));
                          countdown
                        else do
                          countdown));
                      let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                      let ⟨countdown, w⟩ ← (pure
                        (Rust_primitives.Hax.Tuple2.mk
                          countdown Rust_primitives.Hax.Tuple0.mk));
                      Rust_primitives.Hax.Tuple0.mk
                    else do
                      Rust_primitives.Hax.Tuple0.mk))
                else do
                  let should_be_reachable : i32 ← (pure countdown);
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["reached
"])));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              Rust_primitives.Hax.Tuple0.mk))
        else do
          let countdown : i32 ← (pure (0 : i32));
          let countdown : i32 ← (pure
            (← if true then do
              let countdown : i32 ← (pure (1 : i32));
              countdown
            else do
              countdown));
          (← if
          (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
            let countdown : i32 ← (pure (← countdown -? (4 : i32)));
            let ⟨countdown, z⟩ ← (pure
              (Rust_primitives.Hax.Tuple2.mk
                countdown Rust_primitives.Hax.Tuple0.mk));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, w⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk))
          else do
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
              let countdown : i32 ← (pure
                (← if
                (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                    ||? (← Rust_primitives.Hax.Machine_int.gt
                        countdown
                        (5 : i32)))
                  ||? (← Rust_primitives.Hax.Machine_int.ne
                      countdown
                      (9 : i32))) then do
                  let countdown : i32 ← (pure (0 : i32));
                  countdown
                else do
                  countdown));
              let countdown : i32 ← (pure (← countdown -? (5 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              let should_be_reachable : i32 ← (pure countdown);
              let _ ← (pure
                (← Std.Io.Stdio._print
                    (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                        #v["reached
"])));
              let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
              Rust_primitives.Hax.Tuple0.mk)))
      else do
        (← if (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
          let countdown : i32 ← (pure
            (← if
            (← (← (← Rust_primitives.Hax.Machine_int.lt countdown (1 : i32))
                ||? (← Rust_primitives.Hax.Machine_int.gt countdown (5 : i32)))
              ||? (← Rust_primitives.Hax.Machine_int.ne countdown (9 : i32)))
            then do
              let countdown : i32 ← (pure (0 : i32));
              countdown
            else do
              countdown));
          let countdown : i32 ← (pure (← countdown -? (5 : i32)));
          (← if true then do
            let countdown : i32 ← (pure (0 : i32));
            let countdown : i32 ← (pure
              (← if true then do
                let countdown : i32 ← (pure (10 : i32));
                countdown
              else do
                countdown));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let countdown : i32 ← (pure (0 : i32));
              let countdown : i32 ← (pure
                (← if true then do
                  let countdown : i32 ← (pure (1 : i32));
                  countdown
                else do
                  countdown));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, z⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32))
                  then do
                    let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    (← if
                    (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                    then do
                      let countdown : i32 ← (pure
                        (← if
                        (← (← (← Rust_primitives.Hax.Machine_int.lt
                                countdown
                                (1 : i32))
                            ||? (← Rust_primitives.Hax.Machine_int.gt
                                countdown
                                (5 : i32)))
                          ||? (← Rust_primitives.Hax.Machine_int.ne
                              countdown
                              (9 : i32))) then do
                          let countdown : i32 ← (pure (0 : i32));
                          countdown
                        else do
                          countdown));
                      let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                      let ⟨countdown, w⟩ ← (pure
                        (Rust_primitives.Hax.Tuple2.mk
                          countdown Rust_primitives.Hax.Tuple0.mk));
                      Rust_primitives.Hax.Tuple0.mk
                    else do
                      Rust_primitives.Hax.Tuple0.mk))
                else do
                  let should_be_reachable : i32 ← (pure countdown);
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["reached
"])));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let countdown : i32 ← (pure (0 : i32));
                let countdown : i32 ← (pure
                  (← if true then do
                    let countdown : i32 ← (pure (1 : i32));
                    countdown
                  else do
                    countdown));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, z⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32))
                  then do
                    let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    (← if
                    (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                    then do
                      let countdown : i32 ← (pure
                        (← if
                        (← (← (← Rust_primitives.Hax.Machine_int.lt
                                countdown
                                (1 : i32))
                            ||? (← Rust_primitives.Hax.Machine_int.gt
                                countdown
                                (5 : i32)))
                          ||? (← Rust_primitives.Hax.Machine_int.ne
                              countdown
                              (9 : i32))) then do
                          let countdown : i32 ← (pure (0 : i32));
                          countdown
                        else do
                          countdown));
                      let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                      let ⟨countdown, w⟩ ← (pure
                        (Rust_primitives.Hax.Tuple2.mk
                          countdown Rust_primitives.Hax.Tuple0.mk));
                      Rust_primitives.Hax.Tuple0.mk
                    else do
                      Rust_primitives.Hax.Tuple0.mk))
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, z⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    (← if
                    (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32))
                    then do
                      let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                      let ⟨countdown, w⟩ ← (pure
                        (Rust_primitives.Hax.Tuple2.mk
                          countdown Rust_primitives.Hax.Tuple0.mk));
                      Rust_primitives.Hax.Tuple0.mk
                    else do
                      (← if
                      (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                      then do
                        let countdown : i32 ← (pure
                          (← if
                          (← (← (← Rust_primitives.Hax.Machine_int.lt
                                  countdown
                                  (1 : i32))
                              ||? (← Rust_primitives.Hax.Machine_int.gt
                                  countdown
                                  (5 : i32)))
                            ||? (← Rust_primitives.Hax.Machine_int.ne
                                countdown
                                (9 : i32))) then do
                            let countdown : i32 ← (pure (0 : i32));
                            countdown
                          else do
                            countdown));
                        let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                        let ⟨countdown, w⟩ ← (pure
                          (Rust_primitives.Hax.Tuple2.mk
                            countdown Rust_primitives.Hax.Tuple0.mk));
                        Rust_primitives.Hax.Tuple0.mk
                      else do
                        Rust_primitives.Hax.Tuple0.mk))
                  else do
                    let should_be_reachable : i32 ← (pure countdown);
                    let _ ← (pure
                      (← Std.Io.Stdio._print
                          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                              #v["reached
"])));
                    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                Rust_primitives.Hax.Tuple0.mk))
          else do
            let countdown : i32 ← (pure (0 : i32));
            let countdown : i32 ← (pure
              (← if true then do
                let countdown : i32 ← (pure (1 : i32));
                countdown
              else do
                countdown));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
              let countdown : i32 ← (pure (← countdown -? (4 : i32)));
              let ⟨countdown, z⟩ ← (pure
                (Rust_primitives.Hax.Tuple2.mk
                  countdown Rust_primitives.Hax.Tuple0.mk));
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then do
                let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                let ⟨countdown, w⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then
                do
                  let countdown : i32 ← (pure
                    (← if
                    (← (← (← Rust_primitives.Hax.Machine_int.lt
                            countdown
                            (1 : i32))
                        ||? (← Rust_primitives.Hax.Machine_int.gt
                            countdown
                            (5 : i32)))
                      ||? (← Rust_primitives.Hax.Machine_int.ne
                          countdown
                          (9 : i32))) then do
                      let countdown : i32 ← (pure (0 : i32));
                      countdown
                    else do
                      countdown));
                  let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk))
            else do
              (← if
              (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32)) then do
                let countdown : i32 ← (pure
                  (← if
                  (← (← (← Rust_primitives.Hax.Machine_int.lt
                          countdown
                          (1 : i32))
                      ||? (← Rust_primitives.Hax.Machine_int.gt
                          countdown
                          (5 : i32)))
                    ||? (← Rust_primitives.Hax.Machine_int.ne
                        countdown
                        (9 : i32))) then do
                    let countdown : i32 ← (pure (0 : i32));
                    countdown
                  else do
                    countdown));
                let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                let ⟨countdown, z⟩ ← (pure
                  (Rust_primitives.Hax.Tuple2.mk
                    countdown Rust_primitives.Hax.Tuple0.mk));
                (← if
                (← Rust_primitives.Hax.Machine_int.gt countdown (7 : i32)) then
                do
                  let countdown : i32 ← (pure (← countdown -? (4 : i32)));
                  let ⟨countdown, w⟩ ← (pure
                    (Rust_primitives.Hax.Tuple2.mk
                      countdown Rust_primitives.Hax.Tuple0.mk));
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (2 : i32))
                  then do
                    let countdown : i32 ← (pure
                      (← if
                      (← (← (← Rust_primitives.Hax.Machine_int.lt
                              countdown
                              (1 : i32))
                          ||? (← Rust_primitives.Hax.Machine_int.gt
                              countdown
                              (5 : i32)))
                        ||? (← Rust_primitives.Hax.Machine_int.ne
                            countdown
                            (9 : i32))) then do
                        let countdown : i32 ← (pure (0 : i32));
                        countdown
                      else do
                        countdown));
                    let countdown : i32 ← (pure (← countdown -? (5 : i32)));
                    let ⟨countdown, w⟩ ← (pure
                      (Rust_primitives.Hax.Tuple2.mk
                        countdown Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk
                  else do
                    Rust_primitives.Hax.Tuple0.mk))
              else do
                let should_be_reachable : i32 ← (pure countdown);
                let _ ← (pure
                  (← Std.Io.Stdio._print
                      (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                          #v["reached
"])));
                let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                Rust_primitives.Hax.Tuple0.mk)))
        else do
          Rust_primitives.Hax.Tuple0.mk))
    else do
      Rust_primitives.Hax.Tuple0.mk))