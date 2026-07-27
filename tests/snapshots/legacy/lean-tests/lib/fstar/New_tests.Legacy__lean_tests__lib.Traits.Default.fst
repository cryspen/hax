module New_tests.Legacy__lean_tests__lib.Traits.Default
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

(* item error backend: Explicit rejection by a phase in the Hax engine:
a node of kind [Trait_item_default] have been found in the AST

Note: the error was labeled with context `reject_TraitItemDefault`.

Last available AST for this item:

/** @fail(extraction): ssprove(HAX0008), coq(HAX0008), fstar(HAX0008), proverif(HAX0008)*/#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code, unused, unconditional_recursion)]#[feature(register_tool, if_let_guard)]#[feature(coverage_attribute, stmt_expr_attributes, custom_inner_attributes, test,
yield_expr, coroutines, coroutine_trait, no_core, core_intrinsics)]#[register_tool(_hax)]trait t_Easy<Self_>{fn f_dft((self: Self)) -> int{32}}

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0, None); is_local = true; kind = Types.Trait;
      krate = "new_tests";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0, None); is_local = true;
                  kind = Types.Mod; krate = "new_tests";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0, None); is_local = true;
                              kind = Types.Mod; krate = "new_tests";
                              parent =
                              (Some { Types.contents =
                                      { Types.id = 0;
                                        value =
                                        { Types.index = (0, 0, None);
                                          is_local = true; kind = Types.Mod;
                                          krate = "new_tests";
                                          parent =
                                          (Some { Types.contents =
                                                  { Types.id = 0;
                                                    value =
                                                    { Types.index =
                                                      (0, 0, None);
                                                      is_local = true;
                                                      kind = Types.Mod;
                                                      krate = "new_tests";
                                                      parent = None;
                                                      path = [] }
                                                    }
                                                  });
                                          path =
                                          [{ Types.data =
                                             (Types.TypeNs
                                                "legacy__lean_tests__lib");
                                             disambiguator = 0 }
                                            ]
                                          }
                                        }
                                      });
                              path =
                              [{ Types.data =
                                 (Types.TypeNs "legacy__lean_tests__lib");
                                 disambiguator = 0 };
                                { Types.data = (Types.TypeNs "traits");
                                  disambiguator = 0 }
                                ]
                              }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "legacy__lean_tests__lib");
                     disambiguator = 0 };
                    { Types.data = (Types.TypeNs "traits"); disambiguator = 0
                      };
                    { Types.data = (Types.TypeNs "default");
                      disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "legacy__lean_tests__lib");
         disambiguator = 0 };
        { Types.data = (Types.TypeNs "traits"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "default"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "Easy"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Easy usize =
  {
    f_dft_pre = (fun (self: usize) -> true);
    f_dft_post = (fun (self: usize) (out: usize) -> true);
    f_dft = fun (self: usize) -> self +! mk_usize 1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Easy_for_u32: t_Easy u32 = { __marker_trait_t_Easy = () }

(* item error backend: Explicit rejection by a phase in the Hax engine:
a node of kind [Trait_item_default] have been found in the AST

Note: the error was labeled with context `reject_TraitItemDefault`.

Last available AST for this item:

/** @fail(extraction): ssprove(HAX0008), coq(HAX0008), proverif(HAX0008), fstar(HAX0008)*/#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code)]#[allow(unused_variables)]#[allow(dead_code, unused, unconditional_recursion)]#[feature(register_tool, if_let_guard)]#[feature(coverage_attribute, stmt_expr_attributes, custom_inner_attributes, test,
yield_expr, coroutines, coroutine_trait, no_core, core_intrinsics)]#[register_tool(_hax)]trait t_T1<Self_>{#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_f1_pre(_: Self) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_f1_post(_: Self,_: int) -> bool;
fn f_f1(_: Self) -> int;
fn f_f2((self: Self)) -> int{1}
fn f_f3<A>((self: Self,x: A)) -> int{1}
fn f_f4<A>((self: Self,x: A)) -> int where _: new_tests::legacy__lean_tests__lib::traits::default::t_Easy<A>{rust_primitives::hax::machine_int::add(new_tests::legacy__lean_tests__lib::traits::default::f_dft(x),1)}}

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0, None); is_local = true; kind = Types.Trait;
      krate = "new_tests";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0, None); is_local = true;
                  kind = Types.Mod; krate = "new_tests";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0, None); is_local = true;
                              kind = Types.Mod; krate = "new_tests";
                              parent =
                              (Some { Types.contents =
                                      { Types.id = 0;
                                        value =
                                        { Types.index = (0, 0, None);
                                          is_local = true; kind = Types.Mod;
                                          krate = "new_tests";
                                          parent =
                                          (Some { Types.contents =
                                                  { Types.id = 0;
                                                    value =
                                                    { Types.index =
                                                      (0, 0, None);
                                                      is_local = true;
                                                      kind = Types.Mod;
                                                      krate = "new_tests";
                                                      parent = None;
                                                      path = [] }
                                                    }
                                                  });
                                          path =
                                          [{ Types.data =
                                             (Types.TypeNs
                                                "legacy__lean_tests__lib");
                                             disambiguator = 0 }
                                            ]
                                          }
                                        }
                                      });
                              path =
                              [{ Types.data =
                                 (Types.TypeNs "legacy__lean_tests__lib");
                                 disambiguator = 0 };
                                { Types.data = (Types.TypeNs "traits");
                                  disambiguator = 0 }
                                ]
                              }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "legacy__lean_tests__lib");
                     disambiguator = 0 };
                    { Types.data = (Types.TypeNs "traits"); disambiguator = 0
                      };
                    { Types.data = (Types.TypeNs "default");
                      disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "legacy__lean_tests__lib");
         disambiguator = 0 };
        { Types.data = (Types.TypeNs "traits"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "default"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "T1"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

type t_S (v_A: Type0) = | S : usize -> v_A -> t_S v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T1_for_S_of_usize: t_T1 (t_S usize) =
  {
    f_f1_pre = (fun (self: t_S usize) -> true);
    f_f1_post = (fun (self: t_S usize) (out: usize) -> true);
    f_f1 = (fun (self: t_S usize) -> self._0 +! self._1);
    f_f2_pre = (fun (self: t_S usize) -> true);
    f_f2_post = (fun (self: t_S usize) (out: usize) -> true);
    f_f2 = fun (self: t_S usize) -> self._1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T1_for_S_of_bool: t_T1 (t_S bool) =
  {
    f_f1_pre = (fun (self: t_S bool) -> true);
    f_f1_post = (fun (self: t_S bool) (out: usize) -> true);
    f_f1 = (fun (self: t_S bool) -> if self._1 then self._0 else mk_usize 9);
    f_f2_pre = (fun (self: t_S bool) -> true);
    f_f2_post = (fun (self: t_S bool) (out: usize) -> true);
    f_f2 = fun (self: t_S bool) -> self._0 +! mk_usize 1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_T1 (t_S Alloc.String.t_String) =
  {
    f_f1_pre = (fun (self: t_S Alloc.String.t_String) -> true);
    f_f1_post = (fun (self: t_S Alloc.String.t_String) (out: usize) -> true);
    f_f1 = fun (self: t_S Alloc.String.t_String) -> mk_usize 0
  }
