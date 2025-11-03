use super::fmt::{Debug, Display};

pub trait Error: Display + Debug {}
