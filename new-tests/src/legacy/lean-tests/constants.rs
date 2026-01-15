// Tests on constants
#![allow(dead_code)]
#![allow(unused_variables)]

const C1: u32 = 5678;
const C2: u32 = C1 + 1;
const C3: u32 = if true { 890 } else { 9 / 0 };

const fn computation(x: u32) -> u32 {
    x + x + 1
}

const C4: u32 = computation(C1) + C2;

fn test() {
    let x = C1 + 1;
    let y = C2 + C3;
    let z = C4 - C3;
}
