module Test_driver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_TestModule = {
  f_module_name:Alloc.String.t_String;
  f_def_id:Hax_frontend_exporter.Types.Def_id.t_DefId;
  f_test_directives:Alloc.Vec.t_Vec Test_driver.Directives.t_TestDirective Alloc.Alloc.t_Global;
  f_items:Alloc.Vec.t_Vec
    (Hax_frontend_exporter.Types.Def_id.t_DefId &
      Alloc.Vec.t_Vec Test_driver.Directives.t_ItemDirective Alloc.Alloc.t_Global)
    Alloc.Alloc.t_Global
}
