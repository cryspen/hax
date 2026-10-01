(* Translates [%matches? PATTERN] into (fun x -> match x with PATTERN -> true | _ -> false).
   Vendored from https://github.com/wrbs/ppx_matches (MIT License, Copyright (c) 2021 Will
   Robson), as the upstream project is unmaintained and incompatible with ppxlib >= 0.36. *)

open Ppxlib

let name = "matches"

let expand ~ctxt pat guard =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let open Ast_builder.Default in
  let cases =
    [
      case ~lhs:pat ~guard ~rhs:[%expr true];
      case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:[%expr false];
    ]
  in
  [%expr
    fun __ppx_matches_value ->
      [%e pexp_match ~loc [%expr __ppx_matches_value] cases]]

let ext =
  Extension.V3.declare name Extension.Context.expression
    Ast_pattern.(ppat __ __)
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
