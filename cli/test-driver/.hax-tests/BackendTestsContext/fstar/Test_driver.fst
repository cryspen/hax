module Test_driver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_BackendTestsContext = {
  f_tests:Alloc.Vec.t_Vec t_TestModule Alloc.Alloc.t_Global;
  f_backend:Hax_types.Cli_options.t_BackendName;
  f_cache_dir:Std.Path.t_PathBuf
}
