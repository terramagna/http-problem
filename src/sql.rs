#[cfg(feature = "diesel")]
use diesel::{
    r2d2::PoolError,
    result::{DatabaseErrorInformation, DatabaseErrorKind, Error},
};
#[cfg(feature = "tokio-postgres")]
use tokio_postgres::error::{Error as PgError, SqlState};

use crate::{custom::StatusCode, Problem};

/// Create a [`Problem`] instance with no available cause.
///
/// This error is meant to be used when an _unrecoverable_ database error
/// happens. Here, unrecoverable means errors that upper levels doesn't have any
/// means to recover from other than retrying the operation or propagating it
/// up.
#[track_caller]
fn sql_error<M>(msg: M) -> Problem
where
    M: std::error::Error + Send + Sync + 'static,
{
    Problem::from_status(StatusCode::INTERNAL_SERVER_ERROR)
        .with_detail("An unexpected error occurred")
        .with_cause(msg)
}

#[cfg(feature = "diesel")]
impl From<PoolError> for Problem {
    #[track_caller]
    fn from(err: PoolError) -> Self {
        sql_error(err)
    }
}

#[cfg(feature = "diesel")]
impl From<Error> for Problem {
    #[track_caller]
    fn from(err: Error) -> Self {
        match err {
            Error::DatabaseError(kind, info) => match kind {
                DatabaseErrorKind::UniqueViolation => sql_error(UniqueViolation(info.into())),
                DatabaseErrorKind::ForeignKeyViolation => {
                    sql_error(ForeignKeyViolation(info.into()))
                }
                DatabaseErrorKind::__Unknown if info.constraint_name().is_some() => {
                    sql_error(CheckViolation(info.into()))
                }
                _ => sql_error(Error::DatabaseError(kind, info)),
            },
            Error::NotFound => sql_error(NoRowsFound),
            err => sql_error(err),
        }
    }
}

#[cfg(feature = "tokio-postgres")]
impl From<PgError> for Problem {
    #[track_caller]
    fn from(err: PgError) -> Self {
        if let Some(db_err) = err.as_db_error() {
            match db_err.code().clone() {
                SqlState::UNIQUE_VIOLATION => sql_error(UniqueViolation(db_err.into())),
                SqlState::FOREIGN_KEY_VIOLATION => sql_error(ForeignKeyViolation(db_err.into())),
                SqlState::CHECK_VIOLATION => sql_error(CheckViolation(db_err.into())),
                _ => sql_error(err),
            }
        } else {
            sql_error(err)
        }
    }
}

#[cfg(feature = "sqlx")]
impl From<sqlx_core::Error> for Problem {
    #[track_caller]
    fn from(err: sqlx_core::Error) -> Self {
        if let Some(db_err) = err.as_database_error() {
            match db_err.kind() {
                sqlx_core::error::ErrorKind::UniqueViolation => {
                    sql_error(UniqueViolation(db_err.into()))
                }
                sqlx_core::error::ErrorKind::ForeignKeyViolation => {
                    sql_error(ForeignKeyViolation(db_err.into()))
                }
                sqlx_core::error::ErrorKind::CheckViolation => {
                    sql_error(CheckViolation(db_err.into()))
                }
                _ => sql_error(err),
            }
        } else {
            sql_error(err)
        }
    }
}

/// A query returned no rows where it should be.
///
/// This error only happens when a query expect only one row, otherwise, no rows
/// is a valid return from it.
///
/// Returns `500 - Internal Server Error` if not caught. We do this as we only
/// emit such error when the code broke the invariant unexpectedly. If you
/// expect that a query returns no rows, use [`OptionalExtension::optional`] or
/// [`ProblemResultExt::optional`].
///
/// [`OptionalExtension::optional`]: diesel::result::OptionalExtension::optional
/// [`ProblemResultExt::optional`]: crate::ext::ProblemResultExt::optional
pub struct NoRowsFound;

impl std::fmt::Debug for NoRowsFound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NoRowsFound")
    }
}

impl std::fmt::Display for NoRowsFound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("No rows were found where one was expected")
    }
}

impl std::error::Error for NoRowsFound {}

/// A query violated an `UNIQUE` constraint.
///
/// Returns `500 - Internal Server Error` if not caught. We do this as the error
/// is an invariant breakage that the develop MUST handle, either via `ON
/// CONFLICT` clauses, parameter validations, or gracefully converting to
/// [`Conflict`] when the client have _some_ way of solving the conflict (as
/// stated in the [RFC 7231]).
///
/// [`Conflict`]: crate::http::Conflict.
/// [RFC 7231]: https://tools.ietf.org/html/rfc7231#section-6.5.8
pub struct UniqueViolation(DbErrorInfo);

impl UniqueViolation {
    /// The name of the column that the error is associated with.
    pub fn constraint_name(&self) -> Option<&str> {
        self.0.constraint_name.as_deref()
    }

    /// The primary human-readable error message.
    pub fn message(&self) -> &str {
        &self.0.message
    }

    /// Th name of th table the error is associated with.
    pub fn table_name(&self) -> Option<&str> {
        self.0.table_name.as_deref()
    }
}

impl std::fmt::Debug for UniqueViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UniqueViolation")
            .field("table_name", &self.table_name())
            .field("constraint_name", &self.constraint_name())
            .field("message", &self.message())
            .finish()
    }
}

impl std::fmt::Display for UniqueViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

impl std::error::Error for UniqueViolation {}

/// A query violated a `FOREIGN KEY` constraint.
///
/// The same observations of [`UniqueViolation`] applies to this error.
pub struct ForeignKeyViolation(DbErrorInfo);

impl ForeignKeyViolation {
    /// The name of the column that the error is associated with.
    pub fn constraint_name(&self) -> Option<&str> {
        self.0.constraint_name.as_deref()
    }

    /// The primary human-readable error message.
    pub fn message(&self) -> &str {
        &self.0.message
    }

    /// Th name of th table the error is associated with.
    pub fn table_name(&self) -> Option<&str> {
        self.0.table_name.as_deref()
    }
}

impl std::fmt::Debug for ForeignKeyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ForeignKeyViolation")
            .field("table_name", &self.table_name())
            .field("constraint_name", &self.constraint_name())
            .field("message", &self.message())
            .finish()
    }
}

impl std::fmt::Display for ForeignKeyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

impl std::error::Error for ForeignKeyViolation {}

/// A query violated a `CHECK` constraint.
///
/// The same observations of [`UniqueViolation`] applies to this error.
pub struct CheckViolation(DbErrorInfo);

impl CheckViolation {
    /// The name of the column that the error is associated with.
    pub fn constraint_name(&self) -> Option<&str> {
        self.0.constraint_name.as_deref()
    }

    /// The primary human-readable error message.
    pub fn message(&self) -> &str {
        &self.0.message
    }

    /// Th name of th table the error is associated with.
    pub fn table_name(&self) -> Option<&str> {
        self.0.table_name.as_deref()
    }
}

impl std::fmt::Debug for CheckViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckViolation")
            .field("table_name", &self.table_name())
            .field("constraint_name", &self.constraint_name())
            .field("message", &self.message())
            .finish()
    }
}

impl std::fmt::Display for CheckViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

impl std::error::Error for CheckViolation {}

struct DbErrorInfo {
    constraint_name: Option<String>,
    message: String,
    table_name: Option<String>,
}

#[cfg(feature = "diesel")]
impl From<Box<dyn DatabaseErrorInformation + Send + Sync>> for DbErrorInfo {
    fn from(info: Box<dyn DatabaseErrorInformation + Send + Sync>) -> Self {
        Self {
            constraint_name: info.constraint_name().map(String::from),
            message: info.message().to_string(),
            table_name: info.table_name().map(String::from),
        }
    }
}

#[cfg(feature = "tokio-postgres")]
impl From<&'_ tokio_postgres::error::DbError> for DbErrorInfo {
    fn from(err: &'_ tokio_postgres::error::DbError) -> Self {
        Self {
            constraint_name: err.constraint().map(String::from),
            message: err.message().to_string(),
            table_name: err.table().map(String::from),
        }
    }
}

#[cfg(feature = "sqlx")]
impl From<&'_ dyn sqlx_core::error::DatabaseError> for DbErrorInfo {
    fn from(err: &'_ dyn sqlx_core::error::DatabaseError) -> Self {
        Self {
            constraint_name: err.constraint().map(String::from),
            message: err.message().to_string(),
            table_name: err.table().map(String::from),
        }
    }
}
