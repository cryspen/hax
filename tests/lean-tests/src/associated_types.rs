mod basic {
    trait Iterable {
        type Item;
        fn first(&self) -> Self::Item;
    }

    fn just_the_first<I: Iterable>(iter: I) -> I::Item {
        iter.first()
    }

    fn first_plus_1<I: Iterable<Item = i32>>(iter: I) -> i32 {
        iter.first() + 1
    }

    impl Iterable for bool {
        type Item = i32;
        fn first(&self) -> i32 {
            3
        }
    }

    fn a() {
        first_plus_1(true);
    }
}

mod multiple_associated_types {
    trait Pair {
        type First;
        type Second;
        fn first(&self) -> Self::First;
        fn second(&self) -> Self::Second;
    }

    fn get_both<P: Pair>(pair: P) -> (P::First, P::Second) {
        (pair.first(), pair.second())
    }

    impl Pair for (i32, bool) {
        type First = i32;
        type Second = bool;
        fn first(&self) -> i32 {
            self.0
        }
        fn second(&self) -> bool {
            self.1
        }
    }

    fn b() {
        let pair = (42, true);
        let both = get_both(pair);
    }

    fn get_first_as_i32<P: Pair<First = i32>>(pair: P) -> i32 {
        pair.first()
    }
}
