//! @fail(tc): lean(1), fstar(2)
/// @fail(extraction): lean(HAX0001), proverif(HAX0008), coq(HAX0001), fstar(HAX0001)
fn main() {
    if false {
        loop {}
    }
}
