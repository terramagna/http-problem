use std::{error::Error, fmt};

use crate::{
    custom::{CustomProblem, StatusCode, Uri},
    CowStr, Extensions, Problem,
};

/// Create a [`Problem`] instance with a [`BadRequest`] cause.
#[track_caller]
pub fn bad_request(msg: impl Into<CowStr>) -> Problem {
    Problem::from(BadRequest { msg: msg.into() })
}

/// Create a [`Problem`] instance with an [`Unauthorized`] cause.
#[track_caller]
pub fn unauthorized() -> Problem {
    Problem::from(Unauthorized { _inner: () })
}

/// Create a [`Problem`] instance with an [`Forbidden`] cause.
#[track_caller]
pub fn forbidden() -> Problem {
    Problem::from(Forbidden { _inner: () })
}

/// Create a [`Problem`] instance with a [`NotFound`] cause.
#[track_caller]
pub fn not_found(entity: &'static str, identifier: impl fmt::Display) -> Problem {
    Problem::from(NotFound {
        entity,
        identifier: identifier.to_string(),
    })
}

/// Create a [`Problem`] instance with a [`NotFound`] cause with an unknown
/// identifier.
#[track_caller]
pub fn not_found_unknown(entity: &'static str) -> Problem {
    not_found(entity, "<unknown>")
}

/// Create a [`Problem`] instance with a [`Conflict`] cause.
#[track_caller]
pub fn conflict(msg: impl Into<CowStr>) -> Problem {
    Problem::from(Conflict { msg: msg.into() })
}

/// Create a [`Problem`] instance with a [`PreconditionFailed`] cause.
#[track_caller]
pub fn failed_precondition() -> Problem {
    Problem::from(PreconditionFailed { _inner: () })
}

/// Create a [`Problem`] instance with an [`UnprocessableEntity`] cause.
#[track_caller]
pub fn unprocessable(msg: impl Into<CowStr>) -> Problem {
    Problem::from(UnprocessableEntity { msg: msg.into() })
}

/// Create a [`Problem`] instance with no available cause.
///
/// This error is meant to be used when an _unrecoverable_ error happens. Here,
/// unrecoverable means errors that upper levels doesn't have any means to
/// recover from other than retrying the operation or propagating it up.
#[track_caller]
pub fn internal_error<M>(msg: M) -> Problem
where
    M: Error + Send + Sync + 'static,
{
    Problem::from_status(StatusCode::INTERNAL_SERVER_ERROR)
        .with_detail("An unexpected error occurred")
        .with_cause(InternalError {
            inner: Box::new(msg),
        })
}

/// Create a [`Problem`] instance with a [`ServiceUnavailable`] cause.
#[track_caller]
pub fn service_unavailable() -> Problem {
    Problem::from(ServiceUnavailable { _inner: () })
}

macro_rules! http_problem_type {
    ($status: ident) => {
        fn problem_type(&self) -> Uri {
            crate::blank_type_uri()
        }

        fn title(&self) -> &'static str {
            self.status_code().canonical_reason().unwrap()
        }

        fn status_code(&self) -> StatusCode {
            StatusCode::$status
        }
    };

    ($status: ident, display) => {
        http_problem_type!($status);

        fn details(&self) -> CowStr {
            self.to_string().into()
        }
    };

    ($status: ident, details: $detail: expr) => {
        http_problem_type!($status);

        fn details(&self) -> CowStr {
            $detail.into()
        }
    };

    ($status: ident, details <- $detail: ident) => {
        http_problem_type!($status);

        fn details(&self) -> CowStr {
            self.$detail.to_string().into()
        }
    };
}

macro_rules! zst_problem_type {
    ($(#[$doc:meta])+ $name:ident, $status_code:ident, $details:literal) => {
        $(#[$doc])+
        #[derive(Debug, Copy, Clone)]
        pub struct $name {
            _inner: (),
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(stringify!($name))
            }
        }

        impl Error for $name {}

        impl CustomProblem for $name {
            http_problem_type!(
                $status_code,
                details: $details
            );

            fn add_extensions(&self, _: &mut Extensions) {}
        }
    }
}

/// A `400 - Bad Request` error.
///
/// Used when the request is syntactically wrong.
#[derive(Debug)]
pub struct BadRequest {
    msg: CowStr,
}

impl fmt::Display for BadRequest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

impl Error for BadRequest {}

impl CustomProblem for BadRequest {
    http_problem_type!(BAD_REQUEST, details <- msg);

    fn add_extensions(&self, _: &mut Extensions) {}
}

zst_problem_type!(
    /// A `401 - Unauthorized` HTTP error.
    ///
    /// Used when a session doesn't have access to a given service.
    Unauthorized,
    UNAUTHORIZED,
    "You don't have the necessary permissions"
);

zst_problem_type!(
    /// A `403 - Forbidden` HTTP error.
    ///
    /// Used when a session doesn't have access to a given resource.
    Forbidden,
    FORBIDDEN,
    "You don't have the necessary permissions"
);

zst_problem_type!(
    /// A `419 - Precondition Failed` error.
    ///
    /// Used when some precondition in a condition request could not be
    /// satisfied.
    PreconditionFailed,
    PRECONDITION_FAILED,
    "Some request precondition could not be satisfied."
);

/// A `404 - Not Found` error.
///
/// Used when the application expected some entity to exist, but it didn't.
#[derive(Debug)]
pub struct NotFound {
    identifier: String,
    entity: &'static str,
}

impl NotFound {
    /// The type of entity not found.
    pub const fn entity(&self) -> &'static str {
        self.entity
    }
}

impl fmt::Display for NotFound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "The {} identified by '{}' wasn't found",
            self.entity, self.identifier
        )
    }
}

impl Error for NotFound {}

impl CustomProblem for NotFound {
    http_problem_type!(NOT_FOUND, display);

    fn add_extensions(&self, extensions: &mut Extensions) {
        extensions.insert("identifier", &self.identifier);
        extensions.insert("entity", self.entity);
    }
}

/// A `409 - Conflict` error.
///
/// Used when a code invariant was broken due to a client provided information.
#[derive(Debug, Clone)]
pub struct Conflict {
    msg: CowStr,
}

impl fmt::Display for Conflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Conflict: {}", self.msg)
    }
}

impl Error for Conflict {}

impl CustomProblem for Conflict {
    http_problem_type!(CONFLICT, details <- msg);

    fn add_extensions(&self, _: &mut Extensions) {}
}

/// A `422 - Unprocessable Entity` error.
///
/// Used when the received client information doesn't follow the expected
/// interface and requirements.
#[derive(Debug)]
pub struct UnprocessableEntity {
    msg: CowStr,
}

impl fmt::Display for UnprocessableEntity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unprocessable Entity: {}", self.msg)
    }
}

impl Error for UnprocessableEntity {}

impl CustomProblem for UnprocessableEntity {
    http_problem_type!(UNPROCESSABLE_ENTITY, details <- msg);

    fn add_extensions(&self, _: &mut Extensions) {}
}

/// A `500 - Internal Server Error` error.
///
/// Used when there is an unexpected situation or when an unrecoverable error
/// occurs.
#[derive(Debug)]
pub struct InternalError {
    inner: Box<dyn Error + Send + Sync + 'static>,
}

impl fmt::Display for InternalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl Error for InternalError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&*self.inner)
    }
}

zst_problem_type!(
    /// A `503 - Service Unavailable` error.
    ///
    /// Used when a necessary resource for the correctly execution of the
    /// operation was unavailable (e.g. a database connection).
    ServiceUnavailable,
    SERVICE_UNAVAILABLE,
    "The service is currently unavailable, try again after an exponential backoff"
);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_constructor {
        ($test_fn: ident, $constructor: ident, $ty: ty $(,$arg: expr)*) => {
            #[test]
            fn $test_fn() {
                let prd = $constructor($($arg),*);

                assert!(prd.is::<$ty>());
            }
        };
    }

    test_constructor!(test_bad_request, bad_request, BadRequest, "bla");
    test_constructor!(test_unauthorized, unauthorized, Unauthorized);
    test_constructor!(test_forbidden, forbidden, Forbidden);
    test_constructor!(test_not_found, not_found, NotFound, "bla", "foo");
    test_constructor!(test_conflict, conflict, Conflict, "bla");
    test_constructor!(
        test_failed_precondition,
        failed_precondition,
        PreconditionFailed
    );
    test_constructor!(
        test_unprocessable,
        unprocessable,
        UnprocessableEntity,
        "bla"
    );
    test_constructor!(
        test_internal_error,
        internal_error,
        InternalError,
        std::io::Error::new(std::io::ErrorKind::Other, "bla")
    );
    test_constructor!(
        test_service_unavailable,
        service_unavailable,
        ServiceUnavailable
    );
}
