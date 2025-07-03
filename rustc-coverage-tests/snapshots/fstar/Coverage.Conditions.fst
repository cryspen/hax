module Coverage.Conditions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main__v_B: u32 = mk_u32 100

let main (_: Prims.unit) : Prims.unit =
  let countdown:u32 = mk_u32 0 in
  let countdown:u32 =
    if true
    then
      let countdown:u32 = mk_u32 10 in
      countdown
    else countdown
  in
  if countdown >. mk_u32 7
  then
    let countdown:u32 = countdown -! mk_u32 4 in
    let countdown, x:(u32 & u32) = countdown, main__v_B <: (u32 & u32) in
    let countdown:i32 = mk_i32 0 in
    let countdown:i32 =
      if true
      then
        let countdown:i32 = mk_i32 10 in
        countdown
      else countdown
    in
    if countdown >. mk_i32 7
    then
      let countdown:i32 = countdown -! mk_i32 4 in
      if true
      then
        let countdown:i32 = mk_i32 0 in
        let countdown:i32 =
          if true
          then
            let countdown:i32 = mk_i32 10 in
            countdown
          else countdown
        in
        if countdown >. mk_i32 7
        then
          let countdown:i32 = countdown -! mk_i32 4 in
          let countdown:i32 = mk_i32 0 in
          let countdown:i32 =
            if true
            then
              let countdown:i32 = mk_i32 1 in
              countdown
            else countdown
          in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              let should_be_reachable:i32 = countdown in
              let _:Prims.unit =
                Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                      (let list = ["reached\n"] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Core.Fmt.t_Arguments)
              in
              let _:Prims.unit = () in
              ()
        else
          if countdown >. mk_i32 2
          then
            let countdown:i32 =
              if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
              then
                let countdown:i32 = mk_i32 0 in
                countdown
              else countdown
            in
            let countdown:i32 = countdown -! mk_i32 5 in
            let countdown:i32 = mk_i32 0 in
            let countdown:i32 =
              if true
              then
                let countdown:i32 = mk_i32 1 in
                countdown
              else countdown
            in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                let should_be_reachable:i32 = countdown in
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["reached\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
      else
        let countdown:i32 = mk_i32 0 in
        let countdown:i32 =
          if true
          then
            let countdown:i32 = mk_i32 1 in
            countdown
          else countdown
        in
        if countdown >. mk_i32 7
        then
          let countdown:i32 = countdown -! mk_i32 4 in
          let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
            ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              ()
        else
          if countdown >. mk_i32 2
          then
            let countdown:i32 =
              if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
              then
                let countdown:i32 = mk_i32 0 in
                countdown
              else countdown
            in
            let countdown:i32 = countdown -! mk_i32 5 in
            let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
          else
            let should_be_reachable:i32 = countdown in
            let _:Prims.unit =
              Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                    (let list = ["reached\n"] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  Core.Fmt.t_Arguments)
            in
            let _:Prims.unit = () in
            ()
    else
      if countdown >. mk_i32 2
      then
        let countdown:i32 =
          if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
          then
            let countdown:i32 = mk_i32 0 in
            countdown
          else countdown
        in
        let countdown:i32 = countdown -! mk_i32 5 in
        if true
        then
          let countdown:i32 = mk_i32 0 in
          let countdown:i32 =
            if true
            then
              let countdown:i32 = mk_i32 10 in
              countdown
            else countdown
          in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown:i32 = mk_i32 0 in
            let countdown:i32 =
              if true
              then
                let countdown:i32 = mk_i32 1 in
                countdown
              else countdown
            in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                let should_be_reachable:i32 = countdown in
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["reached\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown:i32 = mk_i32 0 in
              let countdown:i32 =
                if true
                then
                  let countdown:i32 = mk_i32 1 in
                  countdown
                else countdown
              in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  if countdown >. mk_i32 7
                  then
                    let countdown:i32 = countdown -! mk_i32 4 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
                  else
                    if countdown >. mk_i32 2
                    then
                      let countdown:i32 =
                        if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                        then
                          let countdown:i32 = mk_i32 0 in
                          countdown
                        else countdown
                      in
                      let countdown:i32 = countdown -! mk_i32 5 in
                      let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                      ()
                else
                  let should_be_reachable:i32 = countdown in
                  let _:Prims.unit =
                    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["reached\n"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  let _:Prims.unit = () in
                  ()
        else
          let countdown:i32 = mk_i32 0 in
          let countdown:i32 =
            if true
            then
              let countdown:i32 = mk_i32 1 in
              countdown
            else countdown
          in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              let should_be_reachable:i32 = countdown in
              let _:Prims.unit =
                Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                      (let list = ["reached\n"] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Core.Fmt.t_Arguments)
              in
              let _:Prims.unit = () in
              ()
  else
    if countdown >. mk_u32 2
    then
      let countdown:u32 =
        if countdown <. mk_u32 1 || countdown >. mk_u32 5 || countdown <>. mk_u32 9
        then
          let countdown:u32 = mk_u32 0 in
          countdown
        else countdown
      in
      let countdown:u32 = countdown -! mk_u32 5 in
      let countdown, x:(u32 & u32) = countdown, countdown <: (u32 & u32) in
      let countdown:i32 = mk_i32 0 in
      let countdown:i32 =
        if true
        then
          let countdown:i32 = mk_i32 10 in
          countdown
        else countdown
      in
      if countdown >. mk_i32 7
      then
        let countdown:i32 = countdown -! mk_i32 4 in
        if true
        then
          let countdown:i32 = mk_i32 0 in
          let countdown:i32 =
            if true
            then
              let countdown:i32 = mk_i32 10 in
              countdown
            else countdown
          in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown:i32 = mk_i32 0 in
            let countdown:i32 =
              if true
              then
                let countdown:i32 = mk_i32 1 in
                countdown
              else countdown
            in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                let should_be_reachable:i32 = countdown in
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["reached\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown:i32 = mk_i32 0 in
              let countdown:i32 =
                if true
                then
                  let countdown:i32 = mk_i32 1 in
                  countdown
                else countdown
              in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  if countdown >. mk_i32 7
                  then
                    let countdown:i32 = countdown -! mk_i32 4 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
                  else
                    if countdown >. mk_i32 2
                    then
                      let countdown:i32 =
                        if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                        then
                          let countdown:i32 = mk_i32 0 in
                          countdown
                        else countdown
                      in
                      let countdown:i32 = countdown -! mk_i32 5 in
                      let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                      ()
                else
                  let should_be_reachable:i32 = countdown in
                  let _:Prims.unit =
                    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["reached\n"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  let _:Prims.unit = () in
                  ()
        else
          let countdown:i32 = mk_i32 0 in
          let countdown:i32 =
            if true
            then
              let countdown:i32 = mk_i32 1 in
              countdown
            else countdown
          in
          if countdown >. mk_i32 7
          then
            let countdown:i32 = countdown -! mk_i32 4 in
            let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
          else
            if countdown >. mk_i32 2
            then
              let countdown:i32 =
                if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                then
                  let countdown:i32 = mk_i32 0 in
                  countdown
                else countdown
              in
              let countdown:i32 = countdown -! mk_i32 5 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              let should_be_reachable:i32 = countdown in
              let _:Prims.unit =
                Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                      (let list = ["reached\n"] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Core.Fmt.t_Arguments)
              in
              let _:Prims.unit = () in
              ()
      else
        if countdown >. mk_i32 2
        then
          let countdown:i32 =
            if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
            then
              let countdown:i32 = mk_i32 0 in
              countdown
            else countdown
          in
          let countdown:i32 = countdown -! mk_i32 5 in
          if true
          then
            let countdown:i32 = mk_i32 0 in
            let countdown:i32 =
              if true
              then
                let countdown:i32 = mk_i32 10 in
                countdown
              else countdown
            in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown:i32 = mk_i32 0 in
              let countdown:i32 =
                if true
                then
                  let countdown:i32 = mk_i32 1 in
                  countdown
                else countdown
              in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  if countdown >. mk_i32 7
                  then
                    let countdown:i32 = countdown -! mk_i32 4 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
                  else
                    if countdown >. mk_i32 2
                    then
                      let countdown:i32 =
                        if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                        then
                          let countdown:i32 = mk_i32 0 in
                          countdown
                        else countdown
                      in
                      let countdown:i32 = countdown -! mk_i32 5 in
                      let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                      ()
                else
                  let should_be_reachable:i32 = countdown in
                  let _:Prims.unit =
                    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["reached\n"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  let _:Prims.unit = () in
                  ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown:i32 = mk_i32 0 in
                let countdown:i32 =
                  if true
                  then
                    let countdown:i32 = mk_i32 1 in
                    countdown
                  else countdown
                in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  if countdown >. mk_i32 7
                  then
                    let countdown:i32 = countdown -! mk_i32 4 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
                  else
                    if countdown >. mk_i32 2
                    then
                      let countdown:i32 =
                        if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                        then
                          let countdown:i32 = mk_i32 0 in
                          countdown
                        else countdown
                      in
                      let countdown:i32 = countdown -! mk_i32 5 in
                      let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                      ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    if countdown >. mk_i32 7
                    then
                      let countdown:i32 = countdown -! mk_i32 4 in
                      let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                      ()
                    else
                      if countdown >. mk_i32 2
                      then
                        let countdown:i32 =
                          if
                            countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                          then
                            let countdown:i32 = mk_i32 0 in
                            countdown
                          else countdown
                        in
                        let countdown:i32 = countdown -! mk_i32 5 in
                        let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                        ()
                  else
                    let should_be_reachable:i32 = countdown in
                    let _:Prims.unit =
                      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                            (let list = ["reached\n"] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list)
                          <:
                          Core.Fmt.t_Arguments)
                    in
                    let _:Prims.unit = () in
                    ()
          else
            let countdown:i32 = mk_i32 0 in
            let countdown:i32 =
              if true
              then
                let countdown:i32 = mk_i32 1 in
                countdown
              else countdown
            in
            if countdown >. mk_i32 7
            then
              let countdown:i32 = countdown -! mk_i32 4 in
              let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
              if countdown >. mk_i32 7
              then
                let countdown:i32 = countdown -! mk_i32 4 in
                let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                ()
              else
                if countdown >. mk_i32 2
                then
                  let countdown:i32 =
                    if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                    then
                      let countdown:i32 = mk_i32 0 in
                      countdown
                    else countdown
                  in
                  let countdown:i32 = countdown -! mk_i32 5 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
            else
              if countdown >. mk_i32 2
              then
                let countdown:i32 =
                  if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                  then
                    let countdown:i32 = mk_i32 0 in
                    countdown
                  else countdown
                in
                let countdown:i32 = countdown -! mk_i32 5 in
                let countdown, z:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                if countdown >. mk_i32 7
                then
                  let countdown:i32 = countdown -! mk_i32 4 in
                  let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                  ()
                else
                  if countdown >. mk_i32 2
                  then
                    let countdown:i32 =
                      if countdown <. mk_i32 1 || countdown >. mk_i32 5 || countdown <>. mk_i32 9
                      then
                        let countdown:i32 = mk_i32 0 in
                        countdown
                      else countdown
                    in
                    let countdown:i32 = countdown -! mk_i32 5 in
                    let countdown, w:(i32 & Prims.unit) = countdown, () <: (i32 & Prims.unit) in
                    ()
              else
                let should_be_reachable:i32 = countdown in
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["reached\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
