trait Clone {
    fn clone(self) -> Self;
}

impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}
