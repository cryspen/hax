module New_tests.Legacy__dyn__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Printable (v_Self: Type0) (v_S: Type0) = {
  f_stringify_pre:v_Self -> Type0;
  f_stringify_post:v_Self -> v_S -> Type0;
  f_stringify:x0: v_Self
    -> Prims.Pure v_S (f_stringify_pre x0) (fun result -> f_stringify_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Printable i32 Alloc.String.t_String =
  {
    f_stringify_pre = (fun (self: i32) -> true);
    f_stringify_post = (fun (self: i32) (out: Alloc.String.t_String) -> true);
    f_stringify
    =
    fun (self: i32) -> Alloc.String.f_to_string #i32 #FStar.Tactics.Typeclasses.solve self
  }

(* item error backend: Explicit rejection by a phase in the Hax engine:
a node of kind [Dyn] have been found in the AST

Note: the error was labeled with context `reject_Dyn`.

Last available AST for this item:

/// @fail(extraction): proverif(HAX0008), ssprove(HAX0008), coq(HAX0008)
/// @fail(extraction): fstar(HAX0008)
#[allow(dead_code)]
#[allow(dead_code, unused, unconditional_recursion)]
#[feature(register_tool, if_let_guard)]
#[feature(
    coverage_attribute,
    stmt_expr_attributes,
    custom_inner_attributes,
    test,
    yield_expr,
    coroutines,
    coroutine_trait,
    no_core,
    core_intrinsics
)]
#[register_tool(_hax)]
fn print(
    a: dyn (new_tests::legacy__dyn__lib::t_Printable<alloc::string::t_String>),
) -> tuple0 {
    {
        let args: tuple1<alloc::string::t_String> = {
            Tuple1(new_tests::legacy__dyn__lib::f_stringify(a))
        };
        {
            let args: [core_models::fmt::rt::t_Argument; 1] = {
                [
                    core_models::fmt::rt::impl__new_display::<
                        alloc::string::t_String,
                    >(proj_proj_tuple0(args)),
                ]
            };
            {
                let _: tuple0 = {
                    std::io::stdio::e_print(
                        core_models::fmt::rt::impl_1__new_v1::<
                            generic_value!(todo),
                            generic_value!(todo),
                        >(["", "\n"], args),
                    )
                };
                {
                    let _: tuple0 = { Tuple0 };
                    Tuple0
                }
            }
        }
    }
}


Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0, None); is_local = true; kind = Types.Fn;
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
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "legacy__dyn__lib");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "legacy__dyn__lib"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "print"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)
