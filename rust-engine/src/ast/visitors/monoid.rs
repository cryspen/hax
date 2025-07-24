/// A trait representing a *monoid* — an algebraic structure with an identity element and an associative binary operation.
///
/// A type implementing `Monoid` must satisfy the following laws:
///
/// 1. **Identity Law**: For any value `a`, `a.append(Self::identity())` must equal `a`.
/// 2. **Associativity Law**: For any values `a`, `b`, and `c`, `a.append(b).append(c)`
///    must be equivalent to `a.append(b.append(c))`.
///
/// This trait is commonly used in scenarios involving accumulation, folding, or combining values.
///
/// # Examples
///
/// ```rust
/// use hax_rust_engine::ast::visitors::Monoid;
///
/// #[derive(Debug, Clone)]
/// struct Sum(i32);
///
/// impl Monoid for Sum {
///     fn identity() -> Self {
///         Sum(0)
///     }
///
///     fn append(&mut self, other: Self) {
///         self.0 += other.0;
///     }
/// }
/// ```
pub trait Monoid {
    /// Returns the identity element of the monoid.
    ///
    /// The identity element should be such that appending it to any value leaves
    /// that value unchanged.
    fn identity() -> Self;

    /// Appends another value to `self`, modifying `self` in place.
    ///
    /// This operation must be associative: the order in which operations are
    /// performed should not change the result (though not necessarily the internal state).
    fn append(&mut self, right: Self);
}

impl Monoid for usize {
    /// The additive identity for `usize` is `0`.
    #[inline]
    fn identity() -> Self {
        0
    }

    /// Adds `right` onto `self` (in-place), so the operation is the usual integer addition.
    #[inline]
    fn append(&mut self, right: Self) {
        *self += right;
    }
}

impl Monoid for isize {
    /// The additive identity for `isize` is `0`.
    #[inline]
    fn identity() -> Self {
        0
    }

    /// Adds `right` onto `self` (in-place), so the operation is the usual integer addition.
    #[inline]
    fn append(&mut self, right: Self) {
        *self += right;
    }
}
