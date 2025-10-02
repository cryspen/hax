module Test_driver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_BackendTestContext = {
  f_test:t_TestModule;
  f_backend:Hax_types.Cli_options.t_BackendName;
  f_cache_dir:Std.Path.t_PathBuf;
  f_haxmeta:Std.Path.t_PathBuf
}
