trait Clone {
    fn clone(self) -> Self;
}

// In our model, everything is clonable
impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}
