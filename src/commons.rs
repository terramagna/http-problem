use std::fmt;

use crate::{custom::StatusCode, CowStr};

/// An error emitted when an assertion failed to be satisfied.
///
/// Emitted by [`ensure!`].
///
/// [`ensure!`]: crate::ensure
#[derive(Debug, Clone)]
pub struct AssertionError {
    msg: CowStr,
}

impl fmt::Display for AssertionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "assertion failure: {}", self.msg)
    }
}

impl std::error::Error for AssertionError {}

impl AssertionError {
    /// Message stored in this error.
    #[inline(always)]
    pub fn message(&self) -> &str {
        &self.msg
    }

    #[doc(hidden)]
    pub const fn new_static(msg: &'static str) -> Self {
        Self {
            msg: CowStr::Borrowed(msg),
        }
    }

    #[doc(hidden)]
    pub const fn new(msg: String) -> Self {
        Self {
            msg: CowStr::Owned(msg),
        }
    }
}

impl From<AssertionError> for crate::Problem {
    #[track_caller]
    fn from(err: AssertionError) -> Self {
        Self::from_status(StatusCode::INTERNAL_SERVER_ERROR)
            .with_detail("An unexpected error occurred")
            .with_cause(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Problem;

    #[test]
    fn test_assert_static() {
        let err = AssertionError::new_static("bla");
        assert_eq!(err.message(), "bla");

        let prb = Problem::from(err.clone());

        assert_eq!(prb.status(), StatusCode::INTERNAL_SERVER_ERROR);
        assert_ne!(prb.details(), err.message());
    }

    #[test]
    fn test_assert_owned() {
        let err = AssertionError::new("bla".to_string());
        assert_eq!(err.message(), "bla");

        let prb = Problem::from(err.clone());

        assert_eq!(prb.status(), StatusCode::INTERNAL_SERVER_ERROR);
        assert_ne!(prb.details(), err.message());
    }
}
