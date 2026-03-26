use hax_lib::*;

fn op(u: u64) -> u64 {
    u / 2
}

fn f<const N: usize>(mut arr: [u64; N]) -> [u64; N] {
    for i in 0..N {
        arr[i] = op(arr[i]);
    }
    arr
}

#[hax_lib::ensures(|_| { future(arr) == &f(*arr) })]
fn g<const N: usize>(arr: &mut [u64; N]) {
    #[cfg(hax)]
    let _initial = arr.clone();

    for i in 0..(N / 2) {
        hax_lib::loop_invariant!(|i: usize| {
            arr[..2 * i] == f(*arr)[..2 * i] && arr[2 * i..] == _initial[2 * i..]
        });
        arr[2 * i] = op(arr[2 * i]);
        arr[2 * i + 1] = op(arr[2 * i + 1]);
    }
    if N % 2 > 0 {
        arr[N - 1] = op(arr[N - 1])
    }
}
