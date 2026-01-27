#[hax_lib::opaque]
pub fn an_opaque_fn() {}

trait T {
    type A;
    fn f();
}

struct S;

#[hax_lib::opaque]
impl T for S {
    type A = usize;
    fn f() {}
}
