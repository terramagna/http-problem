//! # HTTP Problem-based Error Handling Library
//!
//! This crate provides a general mechanism for error handling based on the
//! [RFC 7807] problem entity with the [`Problem`] type.
//!
//! Users can find many pre-defined errors at the [`http`] and [`sql`] modules.
//!
//! The workflow for error handling with this library is as follow:
//!
//! 1. Use the predefined errors/functions or define a new one with the
//!    [`define_custom_type!`] macro to returns errors in functions that
//!    return [`Result<T, Problem>`] (an alias is provided in the library).
//!     * You can also use the extensions traits [`ResultExt`],
//!       [`ProblemResultExt`], [`OptionExt`] to handle common cases.
//! 2. Catch any desired error with [`ProblemResultExt::catch_err`].
//!
//! [RFC 7807]: https://tools.ietf.org/html/rfc7807
//! [`Problem`]: crate::Problem
//! [`define_custom_type!`]: crate::define_custom_type
//! [`http`]: crate::http
//! [`sql`]: crate::sql
//! [`Result<T, Problem>`]: crate::Result
//! [`ResultExt`]: crate::ext::ResultExt
//! [`ProblemResultExt`]: crate::ext::ProblemResultExt
//! [`OptionExt`]: crate::ext::OptionExt
//! [`ProblemResultExt::catch_err`]: crate::ext::ProblemResultExt::catch_err
use std::{borrow::Cow, collections::HashMap, panic::Location};

use backtrace::Backtrace;
use eyre::EyreContext;
use parking_lot::Once;
use serde::ser::SerializeMap;

mod macros;

#[cfg(feature = "actix")]
mod actix;
#[cfg(feature = "axum")]
mod axum;
mod commons;
mod custom;
pub(crate) use self::custom::*;
mod ext;
/// HTTP related well-known errors.
pub mod http;
/// Definitions for global error reporting.
pub mod reporter;
use self::reporter::Report;
#[cfg(feature = "sql")]
/// SQL related well-known errors.
pub mod sql;

/// Prelude imports for this crate.
pub mod prelude {
    #[cfg(feature = "actix")]
    pub use super::actix::*;
    #[cfg(feature = "axum")]
    pub use super::axum::*;
    #[cfg(feature = "sql")]
    pub use super::sql::*;
    pub use super::{commons::*, custom::*, ext::*, http, Problem, Result};
}

pub(crate) fn blank_type_uri() -> custom::Uri {
    custom::Uri::from_static("about:blank")
}

/// An alias for a static `Cow<str>`.
pub type CowStr = Cow<'static, str>;

/// Convenience alias for functions that can error ouy with [`Problem`].
pub type Result<T, E = Problem> = std::result::Result<T, E>;

fn install() {
    static HOOK_INSTALLED: Once = Once::new();

    HOOK_INSTALLED.call_once(|| {
        eyre::set_hook(Box::new(crate::reporter::capture_handler))
            .expect("Failed to set error hook, maybe install was already called?");
    })
}

/// A [RFC 7807] Problem Error.
///
/// # Error Cause
///
/// This type provides methods to access the inner error cause. Although we
/// store it, we DO NOT send it when serializing the problem, as it would
/// leak implementation details.
///
/// # Backtraces
///
/// Many implementations of the RFC add automatic backtrace to the problem.
/// This is NOT done by this type and MUST NOT be added manually, as exposing
/// the backtrace to the caller will expose implementation details and CAN
/// be source of vulnerabilities.
///
/// # Custom Problem Types
///
/// When an HTTP API needs to define a response that indicates an error
/// condition, it might be appropriate to do so by defining a new problem type.
///
/// New problem type definitions MUST document:
///
/// 1. a type URI (typically, with the "http" or "https" scheme),
/// 2. a title that appropriately describes it (think short), and
/// 3. the HTTP status code for it to be used with.
///
/// A problem type definition MAY specify additional members on the problem
/// details object. For example, an extension might use typed links [RFC 5988]
/// to another resource that can be used by machines to resolve the problem.
///
/// Avoid defining custom problem types, preferring to use standardized HTTP
/// status whenever possible. Custom types should only be defined if no
/// HTTP status code can properly encode the occurred problem. As an example:
///
/// ```ignore
/// {
///     "type": "https://example.com/probs/out-of-credit",
///     "status": 403,
///     "title": "You do not have enough credit",
///     "detail": "Your current balance is 30, but that costs 50",
///     "balance": 30,
///     "accounts": ["/account/12345", "/account/67890"]
/// }
/// ```
///
/// When adding a new problem type, we suggest that the type reference should
/// also be added to the main API gateway page.
///
/// # Error Instances
///
/// We currently do not track error instances (the `instance` field defined
/// in the RFC). This may change in the future.
///
/// [RFC 7807]: https://tools.ietf.org/html/rfc7807
/// [RFC 5988]: https://tools.ietf.org/html/rfc5988
#[derive(Default)]
pub struct Problem {
    inner: Box<ProblemInner>,
}

#[derive(Debug)]
struct ProblemInner {
    r#type: Uri,
    title: CowStr,
    status: StatusCode,
    details: CowStr,
    cause: eyre::Report,
    extensions: Extensions,
}

impl Default for ProblemInner {
    fn default() -> Self {
        Self {
            r#type: blank_type_uri(),
            title: Cow::Borrowed(""),
            status: StatusCode::default(),
            details: Cow::Borrowed(""),
            cause: eyre::Report::msg(""),
            extensions: Extensions::default(),
        }
    }
}

impl ProblemInner {
    fn report(&self) -> &Report {
        self.cause
            .handler()
            .downcast_ref::<Report>()
            .expect("Problem used without installation")
    }
}

impl serde::Serialize for Problem {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;

        map.serialize_entry(&"status", &self.status().as_u16())?;

        if !matches!(self.type_().scheme_str(), None | Some("about")) {
            map.serialize_entry(&"type", &format_args!("{}", self.type_()))?;
        }

        map.serialize_entry(&"title", &self.title())?;
        map.serialize_entry(&"detail", &self.details())?;

        for (k, v) in &self.extensions().inner {
            map.serialize_entry(k, v)?;
        }

        map.end()
    }
}

impl std::fmt::Debug for Problem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.report().debug(self.cause(), f)
    }
}

impl std::fmt::Display for Problem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use eyre::EyreHandler;

        writeln!(
            f,
            "{} - {}: {}",
            self.status(),
            self.title(),
            self.details()
        )?;
        self.inner.report().display(&*self.inner.cause, f)?;

        Ok(())
    }
}

impl std::error::Error for Problem {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(self.cause())
    }
}

impl Problem {
    pub(crate) fn report_as_error(&self) {
        if let Some(reporter) = self::reporter::global_reporter() {
            if reporter.should_report_error(self) {
                reporter.report_error(self);
            }
        }
    }
}

/// [`Problem`] constructors.
impl Problem {
    /// Create a custom problem from the given type.
    ///
    /// See the type's documentation for more information about custom types.
    #[track_caller]
    pub fn custom(status: StatusCode, r#type: Uri) -> Self {
        let mut problem = Self::from_status(status);
        problem.inner.r#type = r#type;
        problem
    }

    /// Create a new problem for the given status code.
    #[track_caller]
    pub fn from_status(status: StatusCode) -> Self {
        install();

        let title = status.canonical_reason().unwrap();
        Self {
            inner: Box::new(ProblemInner {
                title: title.into(),
                cause: eyre::Report::msg(title),
                status,
                ..ProblemInner::default()
            }),
        }
    }

    /// Sets the title for this problem.
    ///
    /// **OBS**: HTTP Status only problems MUST NOT have their title changed.
    ///
    /// This method doesn't protect against this, be sure to follow the spec.
    #[must_use]
    pub fn with_title(mut self, title: impl Into<CowStr>) -> Self {
        self.inner.title = title.into();
        self
    }

    /// Sets the detail for this problem.
    #[must_use]
    pub fn with_detail(mut self, detail: impl Into<CowStr>) -> Self {
        self.inner.details = detail.into();
        self
    }

    /// Sets the error cause for this problem.
    #[must_use]
    #[track_caller]
    pub fn with_cause<E>(mut self, cause: E) -> Self
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        self.inner.cause = eyre::Report::new(cause);
        self
    }

    /// Add a new extension value for the problem.
    ///
    /// The `telemetry` extension is reserved for internal use and the `cause`
    /// extension is reserved for future use.
    ///
    /// # Panics
    ///
    /// Panics if `field == "cause"` or if the serialization of `value` fails.
    #[must_use]
    pub fn with_extension<E, V>(mut self, extension: E, value: V) -> Self
    where
        E: Into<CowStr>,
        V: serde::Serialize,
    {
        let extension = extension.into();
        match extension.as_ref() {
            "type" | "status" | "details" | "cause" | "" => {
                panic!("Invalid extension received: {extension}")
            }
            _ => self.inner.extensions.insert(extension, value),
        }

        self
    }
}

/// Getters
impl Problem {
    /// A URI reference ([RFC 3986]) that identifies the problem type.
    ///
    /// The specification encourages that, when dereferenced, it provide
    /// human-readable documentation for the problem type. When this
    /// member is not present, its value is assumed to be `about:blank`.
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    pub const fn type_(&self) -> &Uri {
        &self.inner.r#type
    }

    /// A short, human-readable summary of the problem type.
    ///
    /// It SHOULD NOT change from occurrence to occurrence of the problem.
    pub fn title(&self) -> &str {
        &self.inner.title
    }

    /// The HTTP status code generated by the origin server for this
    /// occurrence of the problem.
    pub const fn status(&self) -> StatusCode {
        self.inner.status
    }

    /// A human-readable explanation specific to this occurrence of the
    /// problem.
    pub fn details(&self) -> &str {
        &self.inner.details
    }

    /// Extra members of the problem containing additional information
    /// about the specific occurrence.
    pub const fn extensions(&self) -> &Extensions {
        &self.inner.extensions
    }

    /// Extra members of the problem containing additional information
    /// about the specific occurrence.
    pub fn extensions_mut(&mut self) -> &mut Extensions {
        &mut self.inner.extensions
    }

    /// The internal cause of this problem.
    pub fn cause(&self) -> &(dyn std::error::Error + 'static) {
        &*self.inner.cause
    }
}

/// Error handling methods.
impl Problem {
    /// Get the [`Report`] of this instance.
    #[must_use]
    pub fn report(&self) -> &Report {
        self.inner.report()
    }

    /// Get the backtrace for this Error.
    pub fn backtrace(&self) -> Backtrace {
        (*self.inner.report().backtrace()).clone()
    }

    /// Location where this instance was created.
    pub fn location(&self) -> &'static Location<'static> {
        self.inner.report().location()
    }

    /// Returns true if `E` is the type of the cause of this problem.
    ///
    /// Useful to a failed result is caused by a specific error type.
    pub fn is<E>(&self) -> bool
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        self.inner.cause.is::<E>()
    }

    /// Attempts to downcast the problem to a concrete type.
    ///
    /// # Errors
    ///
    /// Returns the original problem if the underlying cause is not of the
    /// specified type.
    pub fn downcast<E>(mut self) -> Result<E, Self>
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        match self.inner.cause.downcast() {
            Ok(err) => Ok(err),
            Err(cause) => {
                self.inner.cause = cause;
                Err(self)
            }
        }
    }

    /// Attempt to downcast the problem to a concrete type by reference.
    pub fn downcast_ref<E>(&self) -> Option<&E>
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        self.inner.cause.downcast_ref()
    }

    /// Attempts to isolate a specific cause to the `Err` variant.
    ///
    /// This is different from a downcast as we don't lose backtrace/source
    /// location information.
    ///
    /// This method is useful when the user wants to handle specific errors
    /// with `?`.
    ///
    /// # Errors
    ///
    /// Returns `Err` when `self` is an `E`.
    pub fn isolate<E>(self) -> Result<Self, Self>
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        if self.is::<E>() {
            Err(self)
        } else {
            Ok(self)
        }
    }
}

/// Set of extensions of a [`Problem`].
#[derive(Debug, Clone, Default, serde::Serialize)]
#[serde(transparent)]
pub struct Extensions {
    inner: HashMap<CowStr, serde_json::Value>,
}

impl Extensions {
    /// Add an extension into the set.
    ///
    /// # Panics
    ///
    /// Panics if the serialization of `V` fails.
    pub fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<CowStr>,
        V: serde::Serialize,
    {
        self.inner.insert(key.into(), serde_json::json!(value));
    }

    /// Number of extensions.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// If we have no extensions.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl<'e> IntoIterator for &'e Extensions {
    type IntoIter = ExtensionsIter<'e>;
    type Item = (&'e str, &'e serde_json::Value);

    fn into_iter(self) -> Self::IntoIter {
        ExtensionsIter(self.inner.iter().map(|(k, v)| (&**k, v)))
    }
}

use std::{collections::hash_map::Iter, iter::Map};

#[doc(hidden)]
#[allow(clippy::type_complexity)]
pub struct ExtensionsIter<'e>(
    Map<
        Iter<'e, Cow<'e, str>, serde_json::Value>,
        for<'a> fn((&'a Cow<'a, str>, &'a serde_json::Value)) -> (&'a str, &'a serde_json::Value),
    >,
);

impl<'e> Iterator for ExtensionsIter<'e> {
    type Item = (&'e str, &'e serde_json::Value);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use serde_json::json;

    use super::*;

    #[test]
    fn test_extensions() {
        let mut ext = Extensions::default();

        assert!(ext.is_empty());
        assert_eq!(ext.len(), 0);
        assert!(ext.into_iter().next().is_none());

        ext.insert("bla", "bla");

        assert_eq!(ext.len(), 1);
        assert!(!ext.is_empty());
        assert_eq!(ext.into_iter().next(), Some(("bla", &json!("bla"))));

        assert_eq!(json!(ext), json!({ "bla": "bla" }));
    }

    #[test]
    fn test_problem_with_extensions_good() {
        let mut error = http::failed_precondition();

        for (key, value) in [
            ("bla", json!("bla")),
            ("foo", json!(1)),
            ("bar", json!(1.2)),
            ("baz", json!([1.2])),
        ] {
            error = error.with_extension(key, value);
        }

        assert_eq!(error.extensions().len(), 4);
    }

    macro_rules! test_invalid_extension {
        ($test_fn: ident, $ext: literal) => {
            #[test]
            #[should_panic = concat!("Invalid extension received: ", $ext)]
            fn $test_fn() {
                let _res = http::failed_precondition().with_extension($ext, json!(1));
            }
        };
    }

    test_invalid_extension!(test_problem_with_extension_type, "type");
    test_invalid_extension!(test_problem_with_extension_status, "status");
    test_invalid_extension!(test_problem_with_extension_details, "details");
    test_invalid_extension!(test_problem_with_extension_cause, "cause");
    test_invalid_extension!(test_problem_with_extension_empty, "");

    #[test]
    fn test_problem_getter_type_() {
        assert_eq!(http::failed_precondition().type_(), "about:blank");
    }

    #[test]
    fn test_problem_getter_report() {
        let err = http::failed_precondition();
        let report = err.report();

        assert_eq!(err.location(), report.location());
    }

    #[test]
    fn test_problem_error_handling() {
        let err = http::failed_precondition();

        assert!(err.is::<http::PreconditionFailed>());
        assert!(err.downcast_ref::<http::PreconditionFailed>().is_some());
        assert!(err.isolate::<http::PreconditionFailed>().is_err());

        let err = http::failed_precondition();
        assert!(!err.is::<http::NotFound>());
        assert!(err.downcast_ref::<http::NotFound>().is_none());
        assert!(err.isolate::<http::NotFound>().is_ok());

        let err = http::failed_precondition();
        assert!(err.downcast::<http::PreconditionFailed>().is_ok());

        let err = http::failed_precondition();
        assert!(err.downcast::<http::NotFound>().is_err());
    }

    #[test]
    fn test_problem_source() {
        let err = http::failed_precondition();
        let source = err.source().unwrap() as *const dyn Error as *const ();
        let cause = err.cause() as *const dyn Error as *const ();

        assert!(core::ptr::eq(source, cause));
    }

    #[test]
    fn test_problem_serialize_no_type() {
        let err = http::failed_precondition()
            .with_detail("Failed a precondition")
            .with_extension("foo", "bar");

        assert_eq!(
            json!(err),
            json!({
                "detail": "Failed a precondition",
                "foo": "bar",
                "status": 412,
                "title": "Precondition Failed",
            })
        );
    }

    #[test]
    fn test_problem_serialize_type() {
        let err = Problem::custom(
            StatusCode::PRECONDITION_FAILED,
            Uri::from_static("https://my.beautiful.error"),
        )
        .with_detail("Failed a precondition")
        .with_extension("foo", "bar");

        assert_eq!(
            json!(err),
            json!({
                "detail": "Failed a precondition",
                "foo": "bar",
                "status": 412,
                "title": "Precondition Failed",
                "type": "https://my.beautiful.error/",
            })
        );
    }
}
