module Coverage.Attr.Trait_impl_inherit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (reject_TraitItemDefault) ExplicitRejection { reason: "a node of kind [Trait_item_default] have been found in the AST" }
Last available AST for this item:

#[<cfg>(any(feature = "json"))]#[feature(coverage_attribute)]#[<cfg>(any(feature = "json", feature = "lean", feature = "fstar", feature =
"fstar-lax", feature = "coq"))]#[feature(coverage_attribute)]#[allow(unused_attributes)]#[allow(dead_code)]#[allow(unreachable_code)]#[feature(register_tool)]#[register_tool(_hax)]trait t_T<Self_>{fn f_f((self: Self)) -> tuple0{{let _: tuple0 = {std::io::stdio::e_print(core::fmt::rt::impl_1__new_const::<generic_value!(todo)>(["default\n"]))};{let _: tuple0 = {Tuple0};Tuple0}}}}

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0, None); is_local = true; kind = Types.Trait;
      krate = "coverage";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0, None); is_local = true;
                  kind = Types.Mod; krate = "coverage";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0, None); is_local = true;
                              kind = Types.Mod; krate = "coverage";
                              parent =
                              (Some { Types.contents =
                                      { Types.id = 0;
                                        value =
                                        { Types.index = (0, 0, None);
                                          is_local = true; kind = Types.Mod;
                                          krate = "coverage"; parent = None;
                                          path = [] }
                                        }
                                      });
                              path =
                              [{ Types.data = (Types.TypeNs "attr");
                                 disambiguator = 0 }
                                ]
                              }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "attr"); disambiguator = 0 };
                    { Types.data = (Types.TypeNs "trait_impl_inherit");
                      disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "attr"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "trait_impl_inherit"); disambiguator = 0
          };
        { Types.data = (Types.TypeNs "T"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T t_S =
  {
    f_f_pre = (fun (self: t_S) -> true);
    f_f_post = (fun (self: t_S) (out: Prims.unit) -> true);
    f_f
    =
    fun (self: t_S) ->
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
              (let list = ["impl S\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  }

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = f_f #t_S #FStar.Tactics.Typeclasses.solve (S <: t_S) in
  ()
