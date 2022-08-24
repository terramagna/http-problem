//! # Standard Error Handling Types Extensions
//!
//! This module provides traits that extends the common error
//! handling types `Result` and `Option` with methods that
//! integrate them with the types defined in this crate.
use std::error::Error;

#[cfg(feature = "diesel")]
use crate::sql::NoRowsFound;
use crate::{
    http::{self, NotFound},
    Result,
};

mod sealed {
    pub trait Sealed {
        type Value;
    }

    impl<T, E> Sealed for Result<T, E> {
        type Value = T;
    }

    impl<T> Sealed for Option<T> {
        type Value = T;
    }
}

/// Extension methods on [`Result`].
///
/// [`Result`]: std::result::Result
pub trait ResultExt: sealed::Sealed + Sized {
    /// Converts this result to an internal error.
    ///
    /// Used when an unrecoverable error happens.
    ///
    /// See [`internal_error`] for more information.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `self` is `Err`.
    ///
    /// [`internal_error`]: crate::http::internal_error
    fn internal(self) -> Result<Self::Value>;
}

impl<T, E> ResultExt for Result<T, E>
where
    E: Error + Send + Sync + 'static,
{
    #[track_caller]
    fn internal(self) -> Result<Self::Value> {
        self.map_err(http::internal_error)
    }
}

/// Extension methods on `Result<T, Problem>`.
pub trait ProblemResultExt: ResultExt {
    /// Catch a specific error type `E`.
    ///
    /// Returns `Ok(Ok(_))` when the source `Result<T>` is a `T`, returns
    /// `Ok(Err(_))` when its is a `Problem` that can downcast to an `E`,
    /// and returns `Err(_)` otherwise.
    ///
    /// Useful when there is a need to handle a specific error differently,
    /// e.g. a [`NotFound`] error.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `self` contains a [`Problem`] which is not an `E`.
    ///
    /// [`Problem`]: crate::Problem
    /// [`NotFound`]: crate::http::NotFound
    fn catch_err<E>(self) -> Result<Result<Self::Value, E>>
    where
        E: Error + Send + Sync + 'static;

    /// Catch a [`NotFound`] and convert it to `None`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `self` contains a [`Problem`] which is not a
    /// [`NotFound`].
    ///
    /// [`Problem`]: crate::Problem
    /// [`NotFound`]: crate::http::NotFound
    fn optional(self) -> Result<Option<Self::Value>>;
}

impl<T> ProblemResultExt for Result<T> {
    fn catch_err<E>(self) -> Result<Result<Self::Value, E>>
    where
        E: Error + Send + Sync + 'static,
    {
        Ok(match self {
            Ok(ok) => Ok(ok),
            Err(err) => Err(err.downcast::<E>()?),
        })
    }

    fn optional(self) -> Result<Option<Self::Value>> {
        match self {
            Ok(ok) => Ok(Some(ok)),
            Err(err) => {
                if let Err(err) = err.downcast::<NotFound>() {
                    #[cfg(feature = "diesel")]
                    err.downcast::<NoRowsFound>()?;
                    #[cfg(not(feature = "diesel"))]
                    return Err(err);
                }

                Ok(None)
            }
        }
    }
}

/// Extension methods on `Option<T>`.
pub trait OptionExt: sealed::Sealed + Sized {
    /// Returns `Ok(_)` if the source is `Some(_)`, otherwise, returns a
    /// `Problem` that can downcast to `NotFound`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when `self` is `None`.
    fn or_not_found<I>(self, entity: &'static str, identifier: I) -> Result<Self::Value>
    where
        I: std::fmt::Display;

    /// It's a wrapper to `or_not_found` to be used when
    /// there is no a specific identifier to entity message.
    ///
    /// Returns `Ok(_)` if the source is `Some(_)`, otherwise, returns a
    /// `Problem` that can downcast to `NotFound`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when `self` is `None`.
    fn or_not_found_unknown(self, entity: &'static str) -> Result<Self::Value>;
}

impl<T> OptionExt for Option<T> {
    #[track_caller]
    fn or_not_found<I>(self, entity: &'static str, identifier: I) -> Result<Self::Value>
    where
        I: std::fmt::Display,
    {
        // Cannot use Option::ok_or_else as it isn't annotated with track_caller.
        if let Some(value) = self {
            Ok(value)
        } else {
            Err(http::not_found(entity, identifier))
        }
    }

    #[track_caller]
    fn or_not_found_unknown(self, entity: &'static str) -> Result<Self::Value> {
        self.or_not_found(entity, "<unknown>")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::http;

    #[test]
    fn test_internal() {
        let res =
            Err(std::io::Error::new(std::io::ErrorKind::Other, "oh no")) as std::io::Result<()>;

        let res = res.internal().unwrap_err();

        assert!(res.is::<http::InternalError>());
    }

    #[test]
    fn test_catch_err() {
        let res =
            Err(std::io::Error::new(std::io::ErrorKind::Other, "oh no")) as std::io::Result<()>;

        let res = res.internal();

        let not_found = res.catch_err::<http::NotFound>().unwrap_err();
        let res = Err(not_found) as crate::Result<()>;

        let res = res.catch_err::<http::InternalError>().unwrap();

        assert!(res.is_err());

        let ok = Ok(()) as crate::Result<()>;

        assert!(ok.catch_err::<http::InternalError>().unwrap().is_ok());
    }

    #[test]
    fn test_optional() {
        let res = Err(http::not_found("user", "bla")) as crate::Result<()>;
        assert!(res.optional().unwrap().is_none());

        let res = Err(http::failed_precondition()) as crate::Result<()>;
        assert!(res.optional().is_err());

        let res = Ok(()) as crate::Result<()>;
        assert!(res.optional().unwrap().is_some());
    }

    #[test]
    fn test_or_not_found() {
        let res = None.or_not_found_unknown("bla") as crate::Result<()>;
        let err = res.unwrap_err();

        assert!(err.is::<http::NotFound>());

        let res = Some(()).or_not_found_unknown("bla");

        assert!(res.is_ok());
    }
}
