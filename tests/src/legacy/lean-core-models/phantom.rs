// Tests for core models in lean
#![allow(dead_code)]
#![allow(unused_variables)]

use core::marker::PhantomData;

trait Foo {}

struct Bar<F: Foo> {
    _phantom: PhantomData<F>,
}

impl<F: Foo> Bar<F> {
    fn new() -> Self {
        Self {_phantom : PhantomData}
    }
}
