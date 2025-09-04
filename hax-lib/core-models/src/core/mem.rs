#[hax_lib::ensures(|res| res == old(dest) && dest == src)]
#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    panic!()
}