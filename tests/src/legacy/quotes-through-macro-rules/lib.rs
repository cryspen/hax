//! Quotation macros invoked through user-side `macro_rules!` wrappers: the
//! antiquotations must still resolve to the caller's locals.
//! @off: coq, ssprove, proverif, legacy-lean

macro_rules! proof {
    ($s:literal) => {
        ::hax_lib::fstar!($s)
    };
}

/// Two levels of wrapping.
macro_rules! proof2 {
    ($s:literal) => {
        proof!($s)
    };
}

fn antiquotes_through_wrappers(x: u32) -> u32 {
    let y = x;
    proof!("assert ($x == $y)");
    proof2!("assert (${x} == ${y})");
    hax_lib::fstar!("assert ($x == $y)");
    y
}
