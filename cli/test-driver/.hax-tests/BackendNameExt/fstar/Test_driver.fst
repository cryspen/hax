module Test_driver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

///\n\nThis is an extension trait for the following impl:\n```rust ,ignore\n#[extension(pub trait BackendNameExt)]\nimpl for BackendName\n\n```
class t_BackendNameExt (v_Self: Type0) = {
  f_job_kind_pre:v_Self -> Test_driver.Log.t_BackendJobKind -> Type0;
  f_job_kind_post:v_Self -> Test_driver.Log.t_BackendJobKind -> Test_driver.Log.t_JobKind -> Type0;
  f_job_kind:x0: v_Self -> x1: Test_driver.Log.t_BackendJobKind
    -> Prims.Pure Test_driver.Log.t_JobKind
        (f_job_kind_pre x0 x1)
        (fun result -> f_job_kind_post x0 x1 result)
}
