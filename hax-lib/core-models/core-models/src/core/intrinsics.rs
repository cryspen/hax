/// See [`core::intrinsics::unreachable`]. UB in Rust; modeled as an unreachable
/// panic, with `requires(false)` so callers must prove it is never hit.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn unreachable() -> ! {
    panic!()
}

#[cfg(test)]
mod tests {
    // Calling `core::intrinsics::unreachable` is UB, so there is nothing to
    // compare against: the model must simply diverge.
    #[test]
    #[should_panic]
    fn test_unreachable() {
        super::unreachable()
    }
}
