fn test_matching(x: u32, c: char, s: &str, b: bool) -> u32 {
    let x = match x {
        0 => 42,
        _ => 0,
    };
    let c = match c {
        'a' => 42,
        _ => 0,
    };
    let s = match s {
        "Hello" => 42,
        _ => 0,
    };
    let b = match b {
        true => 42,
        false => 0,
    };
    return x + c + s + b;
}
