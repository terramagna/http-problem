/// Return early with an [`AssertionError`] if a condition is not satisfied.
///
/// This macro is equivalent to [`assert!`], but returns a [`Problem`] instead
/// of panicking.
///
/// [`AssertionError`]: crate::prelude::AssertionError
/// [`Problem`]: crate::Problem
#[macro_export]
macro_rules! ensure {
    ($check:expr, $msg:literal $(,)?) => {
        if !$check {
            return Err($crate::Problem::from($crate::prelude::AssertionError::new_static($msg)));
        }
    };
    ($check:expr, $($arg:tt)+) => {
        if !$check {
            let msg = format!($($arg)+);
            return Err($crate::Problem::from($crate::prelude::AssertionError::new(msg)));
        }
    }
}

/// Return early with an [`UnprocessableEntity`] if a condition is not
/// satisfied.
///
/// [`UnprocessableEntity`]: crate::http::UnprocessableEntity
#[macro_export]
macro_rules! requires {
    ($check:expr, $msg:literal $(,)?) => {
        if !$check {
            return Err($crate::prelude::http::unprocessable($msg));
        }
    };
    ($check:expr, $($arg:tt)+) => {
        if !$check {
            return Err($crate::prelude::http::unprocessable(format!($($arg)+)));
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_ensure() {
        fn inner(cond: bool) -> crate::Result<()> {
            crate::ensure!(cond, "assertion");

            Ok(())
        }

        assert!(inner(true).is_ok());

        let err = inner(false).unwrap_err();
        assert!(err.is::<crate::prelude::AssertionError>());
    }
}
