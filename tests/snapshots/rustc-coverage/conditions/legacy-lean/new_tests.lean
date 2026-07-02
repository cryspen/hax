
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__conditions

def main.B : u32 := (100 : u32)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let countdown : u32 := (0 : u32);
  let countdown : u32 ←
    if true then do
      let countdown : u32 := (10 : u32);
      (pure countdown)
    else do
      (pure countdown);
  if (← (countdown >? (7 : u32))) then do
    let countdown : u32 ← (countdown -? (4 : u32));
    let ⟨countdown, x⟩ := (rust_primitives.hax.Tuple2.mk countdown main.B);
    let countdown : i32 := (0 : i32);
    let countdown : i32 ←
      if true then do
        let countdown : i32 := (10 : i32);
        (pure countdown)
      else do
        (pure countdown);
    if (← (countdown >? (7 : i32))) then do
      let countdown : i32 ← (countdown -? (4 : i32));
      if true then do
        let countdown : i32 := (0 : i32);
        let countdown : i32 ←
          if true then do
            let countdown : i32 := (10 : i32);
            (pure countdown)
          else do
            (pure countdown);
        if (← (countdown >? (7 : i32))) then do
          let countdown : i32 ← (countdown -? (4 : i32));
          let countdown : i32 := (0 : i32);
          let countdown : i32 ←
            if true then do
              let countdown : i32 := (1 : i32);
              (pure countdown)
            else do
              (pure countdown);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let ⟨countdown, z⟩ :=
              (rust_primitives.hax.Tuple2.mk
                countdown
                rust_primitives.hax.Tuple0.mk);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, w⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              let should_be_reachable : i32 := countdown;
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    (RustArray.ofVec #v["reached\n"]))));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk)
        else do
          if (← (countdown >? (2 : i32))) then do
            let countdown : i32 ←
              if
              (← ((← ((← (countdown <? (1 : i32)))
                  ||? (← (countdown >? (5 : i32)))))
                ||? (← (countdown !=? (9 : i32))))) then do
                let countdown : i32 := (0 : i32);
                (pure countdown)
              else do
                (pure countdown);
            let countdown : i32 ← (countdown -? (5 : i32));
            let countdown : i32 := (0 : i32);
            let countdown : i32 ←
              if true then do
                let countdown : i32 := (1 : i32);
                (pure countdown)
              else do
                (pure countdown);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                let should_be_reachable : i32 := countdown;
                let _ ←
                  (std.io.stdio._print
                    (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                      (RustArray.ofVec #v["reached\n"]))));
                let _ := rust_primitives.hax.Tuple0.mk;
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            (pure rust_primitives.hax.Tuple0.mk)
      else do
        let countdown : i32 := (0 : i32);
        let countdown : i32 ←
          if true then do
            let countdown : i32 := (1 : i32);
            (pure countdown)
          else do
            (pure countdown);
        if (← (countdown >? (7 : i32))) then do
          let countdown : i32 ← (countdown -? (4 : i32));
          let ⟨countdown, z⟩ :=
            (rust_primitives.hax.Tuple2.mk
              countdown
              rust_primitives.hax.Tuple0.mk);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let ⟨countdown, w⟩ :=
              (rust_primitives.hax.Tuple2.mk
                countdown
                rust_primitives.hax.Tuple0.mk);
            (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let ⟨countdown, w⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              (pure rust_primitives.hax.Tuple0.mk)
        else do
          if (← (countdown >? (2 : i32))) then do
            let countdown : i32 ←
              if
              (← ((← ((← (countdown <? (1 : i32)))
                  ||? (← (countdown >? (5 : i32)))))
                ||? (← (countdown !=? (9 : i32))))) then do
                let countdown : i32 := (0 : i32);
                (pure countdown)
              else do
                (pure countdown);
            let countdown : i32 ← (countdown -? (5 : i32));
            let ⟨countdown, z⟩ :=
              (rust_primitives.hax.Tuple2.mk
                countdown
                rust_primitives.hax.Tuple0.mk);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, w⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            let should_be_reachable : i32 := countdown;
            let _ ←
              (std.io.stdio._print
                (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                  (RustArray.ofVec #v["reached\n"]))));
            let _ := rust_primitives.hax.Tuple0.mk;
            (pure rust_primitives.hax.Tuple0.mk)
    else do
      if (← (countdown >? (2 : i32))) then do
        let countdown : i32 ←
          if
          (← ((← ((← (countdown <? (1 : i32)))
              ||? (← (countdown >? (5 : i32)))))
            ||? (← (countdown !=? (9 : i32))))) then do
            let countdown : i32 := (0 : i32);
            (pure countdown)
          else do
            (pure countdown);
        let countdown : i32 ← (countdown -? (5 : i32));
        if true then do
          let countdown : i32 := (0 : i32);
          let countdown : i32 ←
            if true then do
              let countdown : i32 := (10 : i32);
              (pure countdown)
            else do
              (pure countdown);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let countdown : i32 := (0 : i32);
            let countdown : i32 ←
              if true then do
                let countdown : i32 := (1 : i32);
                (pure countdown)
              else do
                (pure countdown);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                let should_be_reachable : i32 := countdown;
                let _ ←
                  (std.io.stdio._print
                    (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                      (RustArray.ofVec #v["reached\n"]))));
                let _ := rust_primitives.hax.Tuple0.mk;
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let countdown : i32 := (0 : i32);
              let countdown : i32 ←
                if true then do
                  let countdown : i32 := (1 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, z⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  if (← (countdown >? (7 : i32))) then do
                    let countdown : i32 ← (countdown -? (4 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    if (← (countdown >? (2 : i32))) then do
                      let countdown : i32 ←
                        if
                        (← ((← ((← (countdown <? (1 : i32)))
                            ||? (← (countdown >? (5 : i32)))))
                          ||? (← (countdown !=? (9 : i32))))) then do
                          let countdown : i32 := (0 : i32);
                          (pure countdown)
                        else do
                          (pure countdown);
                      let countdown : i32 ← (countdown -? (5 : i32));
                      let ⟨countdown, w⟩ :=
                        (rust_primitives.hax.Tuple2.mk
                          countdown
                          rust_primitives.hax.Tuple0.mk);
                      (pure rust_primitives.hax.Tuple0.mk)
                    else do
                      (pure rust_primitives.hax.Tuple0.mk)
                else do
                  let should_be_reachable : i32 := countdown;
                  let _ ←
                    (std.io.stdio._print
                      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                        (RustArray.ofVec #v["reached\n"]))));
                  let _ := rust_primitives.hax.Tuple0.mk;
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              (pure rust_primitives.hax.Tuple0.mk)
        else do
          let countdown : i32 := (0 : i32);
          let countdown : i32 ←
            if true then do
              let countdown : i32 := (1 : i32);
              (pure countdown)
            else do
              (pure countdown);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let ⟨countdown, z⟩ :=
              (rust_primitives.hax.Tuple2.mk
                countdown
                rust_primitives.hax.Tuple0.mk);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, w⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              let should_be_reachable : i32 := countdown;
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    (RustArray.ofVec #v["reached\n"]))));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk)
      else do
        (pure rust_primitives.hax.Tuple0.mk)
  else do
    if (← (countdown >? (2 : u32))) then do
      let countdown : u32 ←
        if
        (← ((← ((← (countdown <? (1 : u32))) ||? (← (countdown >? (5 : u32)))))
          ||? (← (countdown !=? (9 : u32))))) then do
          let countdown : u32 := (0 : u32);
          (pure countdown)
        else do
          (pure countdown);
      let countdown : u32 ← (countdown -? (5 : u32));
      let ⟨countdown, x⟩ := (rust_primitives.hax.Tuple2.mk countdown countdown);
      let countdown : i32 := (0 : i32);
      let countdown : i32 ←
        if true then do
          let countdown : i32 := (10 : i32);
          (pure countdown)
        else do
          (pure countdown);
      if (← (countdown >? (7 : i32))) then do
        let countdown : i32 ← (countdown -? (4 : i32));
        if true then do
          let countdown : i32 := (0 : i32);
          let countdown : i32 ←
            if true then do
              let countdown : i32 := (10 : i32);
              (pure countdown)
            else do
              (pure countdown);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let countdown : i32 := (0 : i32);
            let countdown : i32 ←
              if true then do
                let countdown : i32 := (1 : i32);
                (pure countdown)
              else do
                (pure countdown);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                let should_be_reachable : i32 := countdown;
                let _ ←
                  (std.io.stdio._print
                    (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                      (RustArray.ofVec #v["reached\n"]))));
                let _ := rust_primitives.hax.Tuple0.mk;
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let countdown : i32 := (0 : i32);
              let countdown : i32 ←
                if true then do
                  let countdown : i32 := (1 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, z⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  if (← (countdown >? (7 : i32))) then do
                    let countdown : i32 ← (countdown -? (4 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    if (← (countdown >? (2 : i32))) then do
                      let countdown : i32 ←
                        if
                        (← ((← ((← (countdown <? (1 : i32)))
                            ||? (← (countdown >? (5 : i32)))))
                          ||? (← (countdown !=? (9 : i32))))) then do
                          let countdown : i32 := (0 : i32);
                          (pure countdown)
                        else do
                          (pure countdown);
                      let countdown : i32 ← (countdown -? (5 : i32));
                      let ⟨countdown, w⟩ :=
                        (rust_primitives.hax.Tuple2.mk
                          countdown
                          rust_primitives.hax.Tuple0.mk);
                      (pure rust_primitives.hax.Tuple0.mk)
                    else do
                      (pure rust_primitives.hax.Tuple0.mk)
                else do
                  let should_be_reachable : i32 := countdown;
                  let _ ←
                    (std.io.stdio._print
                      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                        (RustArray.ofVec #v["reached\n"]))));
                  let _ := rust_primitives.hax.Tuple0.mk;
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              (pure rust_primitives.hax.Tuple0.mk)
        else do
          let countdown : i32 := (0 : i32);
          let countdown : i32 ←
            if true then do
              let countdown : i32 := (1 : i32);
              (pure countdown)
            else do
              (pure countdown);
          if (← (countdown >? (7 : i32))) then do
            let countdown : i32 ← (countdown -? (4 : i32));
            let ⟨countdown, z⟩ :=
              (rust_primitives.hax.Tuple2.mk
                countdown
                rust_primitives.hax.Tuple0.mk);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, w⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            if (← (countdown >? (2 : i32))) then do
              let countdown : i32 ←
                if
                (← ((← ((← (countdown <? (1 : i32)))
                    ||? (← (countdown >? (5 : i32)))))
                  ||? (← (countdown !=? (9 : i32))))) then do
                  let countdown : i32 := (0 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              let countdown : i32 ← (countdown -? (5 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              let should_be_reachable : i32 := countdown;
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    (RustArray.ofVec #v["reached\n"]))));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk)
      else do
        if (← (countdown >? (2 : i32))) then do
          let countdown : i32 ←
            if
            (← ((← ((← (countdown <? (1 : i32)))
                ||? (← (countdown >? (5 : i32)))))
              ||? (← (countdown !=? (9 : i32))))) then do
              let countdown : i32 := (0 : i32);
              (pure countdown)
            else do
              (pure countdown);
          let countdown : i32 ← (countdown -? (5 : i32));
          if true then do
            let countdown : i32 := (0 : i32);
            let countdown : i32 ←
              if true then do
                let countdown : i32 := (10 : i32);
                (pure countdown)
              else do
                (pure countdown);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let countdown : i32 := (0 : i32);
              let countdown : i32 ←
                if true then do
                  let countdown : i32 := (1 : i32);
                  (pure countdown)
                else do
                  (pure countdown);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, z⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  if (← (countdown >? (7 : i32))) then do
                    let countdown : i32 ← (countdown -? (4 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    if (← (countdown >? (2 : i32))) then do
                      let countdown : i32 ←
                        if
                        (← ((← ((← (countdown <? (1 : i32)))
                            ||? (← (countdown >? (5 : i32)))))
                          ||? (← (countdown !=? (9 : i32))))) then do
                          let countdown : i32 := (0 : i32);
                          (pure countdown)
                        else do
                          (pure countdown);
                      let countdown : i32 ← (countdown -? (5 : i32));
                      let ⟨countdown, w⟩ :=
                        (rust_primitives.hax.Tuple2.mk
                          countdown
                          rust_primitives.hax.Tuple0.mk);
                      (pure rust_primitives.hax.Tuple0.mk)
                    else do
                      (pure rust_primitives.hax.Tuple0.mk)
                else do
                  let should_be_reachable : i32 := countdown;
                  let _ ←
                    (std.io.stdio._print
                      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                        (RustArray.ofVec #v["reached\n"]))));
                  let _ := rust_primitives.hax.Tuple0.mk;
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let countdown : i32 := (0 : i32);
                let countdown : i32 ←
                  if true then do
                    let countdown : i32 := (1 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, z⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  if (← (countdown >? (7 : i32))) then do
                    let countdown : i32 ← (countdown -? (4 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    if (← (countdown >? (2 : i32))) then do
                      let countdown : i32 ←
                        if
                        (← ((← ((← (countdown <? (1 : i32)))
                            ||? (← (countdown >? (5 : i32)))))
                          ||? (← (countdown !=? (9 : i32))))) then do
                          let countdown : i32 := (0 : i32);
                          (pure countdown)
                        else do
                          (pure countdown);
                      let countdown : i32 ← (countdown -? (5 : i32));
                      let ⟨countdown, w⟩ :=
                        (rust_primitives.hax.Tuple2.mk
                          countdown
                          rust_primitives.hax.Tuple0.mk);
                      (pure rust_primitives.hax.Tuple0.mk)
                    else do
                      (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, z⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    if (← (countdown >? (7 : i32))) then do
                      let countdown : i32 ← (countdown -? (4 : i32));
                      let ⟨countdown, w⟩ :=
                        (rust_primitives.hax.Tuple2.mk
                          countdown
                          rust_primitives.hax.Tuple0.mk);
                      (pure rust_primitives.hax.Tuple0.mk)
                    else do
                      if (← (countdown >? (2 : i32))) then do
                        let countdown : i32 ←
                          if
                          (← ((← ((← (countdown <? (1 : i32)))
                              ||? (← (countdown >? (5 : i32)))))
                            ||? (← (countdown !=? (9 : i32))))) then do
                            let countdown : i32 := (0 : i32);
                            (pure countdown)
                          else do
                            (pure countdown);
                        let countdown : i32 ← (countdown -? (5 : i32));
                        let ⟨countdown, w⟩ :=
                          (rust_primitives.hax.Tuple2.mk
                            countdown
                            rust_primitives.hax.Tuple0.mk);
                        (pure rust_primitives.hax.Tuple0.mk)
                      else do
                        (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    let should_be_reachable : i32 := countdown;
                    let _ ←
                      (std.io.stdio._print
                        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                          (RustArray.ofVec #v["reached\n"]))));
                    let _ := rust_primitives.hax.Tuple0.mk;
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                (pure rust_primitives.hax.Tuple0.mk)
          else do
            let countdown : i32 := (0 : i32);
            let countdown : i32 ←
              if true then do
                let countdown : i32 := (1 : i32);
                (pure countdown)
              else do
                (pure countdown);
            if (← (countdown >? (7 : i32))) then do
              let countdown : i32 ← (countdown -? (4 : i32));
              let ⟨countdown, z⟩ :=
                (rust_primitives.hax.Tuple2.mk
                  countdown
                  rust_primitives.hax.Tuple0.mk);
              if (← (countdown >? (7 : i32))) then do
                let countdown : i32 ← (countdown -? (4 : i32));
                let ⟨countdown, w⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                (pure rust_primitives.hax.Tuple0.mk)
              else do
                if (← (countdown >? (2 : i32))) then do
                  let countdown : i32 ←
                    if
                    (← ((← ((← (countdown <? (1 : i32)))
                        ||? (← (countdown >? (5 : i32)))))
                      ||? (← (countdown !=? (9 : i32))))) then do
                      let countdown : i32 := (0 : i32);
                      (pure countdown)
                    else do
                      (pure countdown);
                  let countdown : i32 ← (countdown -? (5 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  (pure rust_primitives.hax.Tuple0.mk)
            else do
              if (← (countdown >? (2 : i32))) then do
                let countdown : i32 ←
                  if
                  (← ((← ((← (countdown <? (1 : i32)))
                      ||? (← (countdown >? (5 : i32)))))
                    ||? (← (countdown !=? (9 : i32))))) then do
                    let countdown : i32 := (0 : i32);
                    (pure countdown)
                  else do
                    (pure countdown);
                let countdown : i32 ← (countdown -? (5 : i32));
                let ⟨countdown, z⟩ :=
                  (rust_primitives.hax.Tuple2.mk
                    countdown
                    rust_primitives.hax.Tuple0.mk);
                if (← (countdown >? (7 : i32))) then do
                  let countdown : i32 ← (countdown -? (4 : i32));
                  let ⟨countdown, w⟩ :=
                    (rust_primitives.hax.Tuple2.mk
                      countdown
                      rust_primitives.hax.Tuple0.mk);
                  (pure rust_primitives.hax.Tuple0.mk)
                else do
                  if (← (countdown >? (2 : i32))) then do
                    let countdown : i32 ←
                      if
                      (← ((← ((← (countdown <? (1 : i32)))
                          ||? (← (countdown >? (5 : i32)))))
                        ||? (← (countdown !=? (9 : i32))))) then do
                        let countdown : i32 := (0 : i32);
                        (pure countdown)
                      else do
                        (pure countdown);
                    let countdown : i32 ← (countdown -? (5 : i32));
                    let ⟨countdown, w⟩ :=
                      (rust_primitives.hax.Tuple2.mk
                        countdown
                        rust_primitives.hax.Tuple0.mk);
                    (pure rust_primitives.hax.Tuple0.mk)
                  else do
                    (pure rust_primitives.hax.Tuple0.mk)
              else do
                let should_be_reachable : i32 := countdown;
                let _ ←
                  (std.io.stdio._print
                    (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                      (RustArray.ofVec #v["reached\n"]))));
                let _ := rust_primitives.hax.Tuple0.mk;
                (pure rust_primitives.hax.Tuple0.mk)
        else do
          (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__conditions

