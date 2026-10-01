//! @fail(tc): legacy-lean(1), fstar(2)
#![allow(unused_assignments, unused_variables)]

#[rustfmt::skip]
/// @fail(extraction): fstar(HAX0001), proverif(HAX0008), ssprove(HAX0001), coq(HAX0001, HAX0001), legacy-lean(HAX0001)
fn main() {
    let result
        =
            loop
        {
            break
            10
            ;
        }
    ;
}
