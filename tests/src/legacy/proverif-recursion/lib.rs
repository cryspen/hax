//! @fail(extraction): proverif(HAX0008, HAX0008, HAX0008)
//! @off: fstar, lean, coq, ssprove
//!
//! A function in a call-graph cycle has no ProVerif encoding, so it is
//! rejected with a diagnostic and opacified to an uninterpreted `fun`. A
//! non-recursive caller stays a `letfun`.

fn count_down(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        count_down(n - 1)
    }
}

fn ping(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        pong(n - 1)
    }
}

fn pong(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        ping(n - 1)
    }
}

fn caller(n: u32) -> u32 {
    count_down(n)
}
