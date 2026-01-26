module Core_models.Ops.Index.Index_mut
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

(* item error backend: The mutation of this [1m&mut[0m is not allowed here.

This is discussed in issue https://github.com/hacspec/hax/issues/420.
Please upvote or comment this issue if you see this error message.
[90mNote: the error was labeled with context `DirectAndMut`.
[0m
Last available AST for this item:

#[allow(dead_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
trait t_IndexMut<Self_, Idx>
where
    _: core_models::ops::index::t_Index<Self, Idx>,
{
    #[allow(dead_code)]
    #[feature(register_tool)]
    #[register_tool(_hax)]
    fn f_index_mut<Anonymous: 'unk>(
        _: Self,
        _: Idx,
    ) -> tuple2<Self, &mut proj_asso_type!()>;
}


Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0, None); is_local = true; kind = Types.Trait;
      krate = "core_models";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0, None); is_local = true;
                  kind = Types.Mod; krate = "core_models";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0, None); is_local = true;
                              kind = Types.Mod; krate = "core_models";
                              parent =
                              (Some { Types.contents =
                                      { Types.id = 0;
                                        value =
                                        { Types.index = (0, 0, None);
                                          is_local = true; kind = Types.Mod;
                                          krate = "core_models";
                                          parent =
                                          (Some { Types.contents =
                                                  { Types.id = 0;
                                                    value =
                                                    { Types.index =
                                                      (0, 0, None);
                                                      is_local = true;
                                                      kind = Types.Mod;
                                                      krate = "core_models";
                                                      parent = None;
                                                      path = [] }
                                                    }
                                                  });
                                          path =
                                          [{ Types.data =
                                             (Types.TypeNs "ops");
                                             disambiguator = 0 }
                                            ]
                                          }
                                        }
                                      });
                              path =
                              [{ Types.data = (Types.TypeNs "ops");
                                 disambiguator = 0 };
                                { Types.data = (Types.TypeNs "index");
                                  disambiguator = 0 }
                                ]
                              }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "ops"); disambiguator = 0 };
                    { Types.data = (Types.TypeNs "index"); disambiguator = 0
                      };
                    { Types.data = (Types.TypeNs "index_mut");
                      disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "ops"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "index"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "index_mut"); disambiguator = 0 };
        { Types.data = (Types.TypeNs "IndexMut"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)
