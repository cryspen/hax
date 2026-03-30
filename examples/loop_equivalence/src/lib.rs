use hax_lib::*;

fn op(u: u64) -> u64 {
    u / 2
}

fn f<const N: usize>(mut arr: [u64; N]) -> [u64; N] {
    #[cfg(hax)]
    let _initial = arr.clone();

    for i in 0..N {
        hax_lib::loop_invariant!(|i: usize| {
            hax_lib::forall(|j: usize| {
                if j < i {
                    arr[j] == op(_initial[j])
                } else if j < N {
                    arr[j] == _initial[j]
                } else {
                    true
                }
            })
        });
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
            hax_lib::forall(|j: usize| {
                if j < 2 * i {
                    arr[j] == op(_initial[j])
                } else if j < N {
                    arr[j] == _initial[j]
                } else {
                    true
                }
            })
        });
        arr[2 * i] = op(arr[2 * i]);
        arr[2 * i + 1] = op(arr[2 * i + 1]);
    }
    if N % 2 > 0 {
        arr[N - 1] = op(arr[N - 1])
    }
}
