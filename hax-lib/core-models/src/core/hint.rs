#[hax_lib::ensures(|res| fstar!("$res == $dummy"))]
pub fn black_box<T>(dummy: T) -> T {
    dummy
}

#[hax_lib::ensures(|res| fstar!("$res == $value"))]
pub fn must_use<T>(value: T) -> T {
    value
}
