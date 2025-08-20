#![allow(dead_code)]

const FORTYTWO: usize = 42;
const MINUS_FORTYTWO: isize = -42;

fn returns42() -> usize {
    FORTYTWO
}

fn add_two_numbers(x: usize, y: usize) -> usize {
    x + y
}

fn letBinding(x: usize, y: usize) -> usize {
    let useless = ();
    let result1 = x + y;
    let result2 = result1 + 2;
    result2 + 1
}

fn closure() -> i32 {
    let x = 41;
    let f1 = |y| y + x;
    let f2 = |y, z| y + x + z;
    f1(1) + f2(2, 3)
}

#[hax_lib::lean::before("@[spec]")]
fn test_before_verbatime_single_line(x: u8) -> u8 {
    42
}

#[hax_lib::lean::before(
    "
def multiline : Unit := ()

"
)]
fn test_before_verbatim_multi_line(x: u8) -> u8 {
    32
}

// BinOp Resugarings
fn binop_resugarings(x: u32) -> u32 {
    x + 1 - 2 * 3 % 4 / 5 >> 1
}

// Enums
// Copy pasted from https://doc.rust-lang.org/rust-by-example/custom_types/enum.html

// Create an `enum` to classify a web event. Note how both
// names and type information together specify the variant:
// `PageLoad != PageUnload` and `KeyPress(char) != Paste(String)`.
// Each is different and independent.
enum WebEvent {
    // An `enum` variant may either be `unit-like`,
    PageLoad,
    PageUnload,
    // like tuple structs,
    KeyPress(char),
    Paste(usize),
    // or c-like structures.
    Click { x: i64, y: i64 },
}

// A function which takes a `WebEvent` enum as an argument and
// returns nothing.
fn inspect(event: WebEvent) {
    match event {
        WebEvent::PageLoad | WebEvent::PageUnload => (),
        // Destructure `c` from inside the `enum` variant.
        WebEvent::KeyPress(c) => (),
        WebEvent::Paste(s) => (),
        // Destructure `Click` into `x` and `y`.
        WebEvent::Click { x, y } => (),
    }
}

fn main_enum() {
    let pressed = WebEvent::KeyPress('x');
    // `to_owned()` creates an owned `String` from a string slice.
    let pasted = WebEvent::Paste(56);
    let click = WebEvent::Click { x: 20, y: 80 };
    let load = WebEvent::PageLoad;
    let unload = WebEvent::PageUnload;

    inspect(pressed);
    inspect(pasted);
    inspect(click);
    inspect(load);
    inspect(unload);
    ()
}
