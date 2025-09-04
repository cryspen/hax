trait PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    fn eq(&self, rhs: &Rhs) -> bool;
}

trait Eq: PartialEq<Self> {}

enum Ordering {
    Less,
    Equal,
    Greater,
}

trait PartialOrd<Rhs>: PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    fn partial_cmp(&self, rhs: &Rhs) -> super::option::Option<Ordering>;
}

fn lt<S, Rhs>(s: &S, rhs: &Rhs) -> bool
where
    S: PartialOrd<Rhs>,
{
    match s.partial_cmp(rhs) {
        super::option::Option::Some(Ordering::Less) => true,
        _ => false,
    }
}

fn le<S, Rhs>(s: &S, rhs: &Rhs) -> bool
where
    S: PartialOrd<Rhs>,
{
    match s.partial_cmp(rhs) {
        super::option::Option::Some(Ordering::Greater) => false,
        _ => true,
    }
}

fn gt<S, Rhs>(s: &S, rhs: &Rhs) -> bool
where
    S: PartialOrd<Rhs>,
{
    match s.partial_cmp(rhs) {
        super::option::Option::Some(Ordering::Greater) => true,
        _ => false,
    }
}

fn ge<S, Rhs>(s: &S, rhs: &Rhs) -> bool
where
    S: PartialOrd<Rhs>,
{
    match s.partial_cmp(rhs) {
        super::option::Option::Some(Ordering::Less) => false,
        _ => true,
    }
}

trait Ord: Eq + PartialOrd<Self> {
    fn cmp(&self, rhs: &Self) -> Ordering;
}

// We need impls for integer types. Has to be done manually if ints are defined manually
