/// See [`core::intrinsics::unreachable`]. UB in Rust; modeled as an unreachable
/// panic, with `requires(false)` so callers must prove it is never hit.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn unreachable() -> ! {
    panic!()
}
