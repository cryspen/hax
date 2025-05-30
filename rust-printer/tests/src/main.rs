mod my_mod {
    pub fn index(index: usize, values: &[u8]) -> u8 {
        values[index]
    }
}

fn my_main() {
    let values = [1u8, 2, 3];
    my_mod::index(1, &values);
}

fn main() {}
