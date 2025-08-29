#![allow(dead_code)]

pub mod structs;

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
    Paste(usize, usize),
    // or c-like structures.
    Click { x: i64, y: i64 },
}

// A function which takes a `WebEvent` enum as an argument and
// returns nothing.
fn inspect(event: WebEvent) {
    match event {
        WebEvent::PageLoad | WebEvent::PageUnload => (),
        WebEvent::KeyPress(c) => (),
        WebEvent::Paste(s1, s2) => (),
        WebEvent::Click {
            x: other_name_for_x,
            y,
        } => (),
    }
}

fn main_enum() {
    let pressed = WebEvent::KeyPress('x');
    // `to_owned()` creates an owned `String` from a string slice.
    let pasted = WebEvent::Paste(56, 42);
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

// Builtin
fn main_tuples() {
    let t0: () = ();
    let t1: (usize,) = (42,);
    let t2: (usize, isize) = (42, 41);
    let t3: (u32, u64, u8) = (1, 2, 3);
}

// Structs

struct TestingEscapeOfReservedKeywords {
    end: u8,
    theorem: u8,
    def: u8,
    abbrev: u8,
}

fn test_reserved_keywords() {
    let t = TestingEscapeOfReservedKeywords {
        end: 0,
        theorem: 1,
        def: 2,
        abbrev: 3,
    };
    let TestingEscapeOfReservedKeywords {
        end,
        theorem,
        def,
        abbrev,
    } = t;
    ()
}

// Structs
// taken (and adapted) from https://doc.rust-lang.org/rust-by-example/custom_types/structs.html

struct Person {
    name: String,
    age: u8,
}

// A unit struct
struct MyUnit;

// A tuple struct
struct Pair(i32, i64);

// A struct with two fields
struct Point {
    x: i64,
    y: i64,
}

// Structs can be reused as fields of another struct
struct Rectangle {
    // A rectangle can be specified by where the top left and bottom right
    // corners are in space.
    top_left: Point,
    bottom_right: Point,
}

fn main_structs() {
    // Create struct with field init shorthand
    let name = String::from("Peter");
    let age = 27;
    let peter = Person { name, age };

    // Instantiate a `Point`
    let point: Point = Point { x: 5, y: 0 };
    let another_point: Point = Point { x: 10, y: 0 };

    // Access the fields of the point
    // [UNSUPORTED YET] let _ = point.x;
    // [UNSUPORTED YET] let _ = point.y;

    // Make a new point by using struct update syntax to use the fields of our
    // other one
    // [UNSUPORTED YET] let bottom_right = Point {
    //     x: 10,
    //     ..another_point
    // };

    // `bottom_right.y` will be the same as `another_point.y` because we used that field
    // from `another_point`

    // Access the fields of the point
    // [UNSUPORTED YET] let _ = bottom_right.x;
    // [UNSUPORTED YET] let _ = bottom_right.y;

    // Destructure the point using a `let` binding
    // [UNSUPORTED YET] let Point {
    //     x: left_edge,
    //     y: top_edge,
    // } = point;

    let _rectangle = Rectangle {
        // struct instantiation is an expression too
        top_left: Point { x: 0, y: 1 },
        bottom_right: point,
    };

    // Instantiate a unit struct
    let _unit = MyUnit;

    // Instantiate a tuple struct
    let pair = Pair(1, 0);

    // Access the fields of a tuple struct
    // [UNSUPORTED YET] let _ = pair.0;
    // [UNSUPORTED YET] let _ = pair.1;

    // Destructure a tuple struct
    // [UNSUPORTED YET] let Pair(integer, decimal) = pair;
}
