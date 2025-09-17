pub const fn black_box<T>(dummy: T) -> T {
    dummy
}

pub const fn must_use<T>(value: T) -> T {
    value
}
