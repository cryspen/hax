use super::fmt::{Debug, Display};

/// See [`std::error::Error`]
pub trait Error: Display + Debug {}
