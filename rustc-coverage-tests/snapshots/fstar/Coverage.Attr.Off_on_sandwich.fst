module Coverage.Attr.Off_on_sandwich
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let do_stuff (_: Prims.unit) : Prims.unit = ()

let dense_a__dense_b__dense_c (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

let dense_a__dense_b (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = dense_a__dense_b__dense_c () in
  let _:Prims.unit = dense_a__dense_b__dense_c () in
  ()

let dense_a (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = dense_a__dense_b () in
  let _:Prims.unit = dense_a__dense_b () in
  ()

let sparse_a__sparse_b__sparse_c__sparse_d__sparse_e (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

let sparse_a__sparse_b__sparse_c__sparse_d (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = sparse_a__sparse_b__sparse_c__sparse_d__sparse_e () in
  let _:Prims.unit = sparse_a__sparse_b__sparse_c__sparse_d__sparse_e () in
  ()

let sparse_a__sparse_b__sparse_c (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = sparse_a__sparse_b__sparse_c__sparse_d () in
  let _:Prims.unit = sparse_a__sparse_b__sparse_c__sparse_d () in
  ()

let sparse_a__sparse_b (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = sparse_a__sparse_b__sparse_c () in
  let _:Prims.unit = sparse_a__sparse_b__sparse_c () in
  ()

let sparse_a (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = sparse_a__sparse_b () in
  let _:Prims.unit = sparse_a__sparse_b () in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = dense_a () in
  let _:Prims.unit = sparse_a () in
  ()
