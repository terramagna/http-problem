use std::{
    error::Error,
    fmt::{self, Debug},
    ops::Deref,
    panic::Location,
};

use backtrace::Backtrace;
use chrono::{DateTime, Local};
use http::Extensions;
use once_cell::sync::OnceCell;
use parking_lot::RwLock;

use crate::Problem;

static REPORTER: OnceCell<Box<dyn ProblemReporter + Send + Sync>> = OnceCell::new();

#[track_caller]
pub(crate) fn capture_handler(error: &(dyn Error + 'static)) -> Box<dyn eyre::EyreHandler> {
    let mut report = Box::default();

    if let Some(reporter) = global_reporter() {
        reporter.capture_error_context(&mut report, error);
    }

    report
}

pub(crate) fn global_reporter() -> Option<&'static dyn ProblemReporter> {
    REPORTER.get().map(|r| &**r as &'static dyn ProblemReporter)
}

/// Sets the current global reporter.
///
/// # Panics
///
/// This function panics if it is called twice.
pub fn set_global_reporter<R>(reporter: R)
where
    R: ProblemReporter + Send + Sync + 'static,
{
    // Can't use `.expect` as `R` is not (and should not) be `Debug`.
    if REPORTER.set(Box::new(reporter)).is_err() {
        panic!("Global problem reporter set twice! Did you call `problem::reporter::set_global_reporter` twice?");
    }
}

/// A type responsible for capturing and report [`Problem`] errors.
///
/// The crate doesn't provide a default implementation of this trait,
/// as how you report your service's errors depends on your infrastructure.
pub trait ProblemReporter {
    /// Capture extra information about the error context and saves it
    /// inside the given report.
    ///
    /// Note that this will be called even for client-related errors,
    /// like NotFound or UnprocessableEntity, during the error _creation_
    /// (this is why we don't pass a [`Problem`] instance here). So try
    /// to be conservative on what you do in this method to prevent making
    /// error handling an expensive operation.
    fn capture_error_context(&'static self, report: &mut Report, error: &(dyn Error + 'static));

    /// Says if we should report the error or not.
    fn should_report_error(&'static self, problem: &Problem) -> bool;

    /// Reports the error.
    ///
    /// This will only be called if [`ProblemReporter::should_report_error`]
    /// returns `true`.
    fn report_error(&'static self, problem: &Problem);
}

/// Location dependent problem report content.
///
/// This type contains information about a given error, primarily the
/// backtrace, location and timestamp of the error, although reporters may
/// include extra information.
///
/// Note that the [`Backtrace`] is NOT resolved during creation, to prevent
/// wasting time on the creation of non-reported errors.
pub struct Report {
    backtrace: RwLock<Backtrace>,
    location: &'static Location<'static>,
    timestamp: DateTime<Local>,
    extensions: Extensions,
}

impl Default for Report {
    #[track_caller]
    fn default() -> Self {
        Self {
            backtrace: RwLock::new(Backtrace::new_unresolved()),
            location: Location::caller(),
            timestamp: Local::now(),
            extensions: Extensions::new(),
        }
    }
}

impl Report {
    /// Resolves and returns a reference to the error backtrace.
    pub fn backtrace(&self) -> impl Deref<Target = Backtrace> + '_ {
        self.backtrace.write().resolve();
        self.backtrace.read()
    }

    /// Returns a reference to the _unresolved_ backtrace.
    #[inline(always)]
    pub fn backtrace_unresolved(&self) -> impl Deref<Target = Backtrace> + '_ {
        self.backtrace.read()
    }

    /// Returns the location where the error happened.
    ///
    /// We try our best to fetch the correct location of the error by
    /// marking everything that may create a [`Problem`] with `#[track_caller]`.
    #[inline(always)]
    pub fn location(&self) -> &'static Location<'static> {
        self.location
    }

    /// Returns the timestamp of when the error was captured.
    #[inline(always)]
    pub fn timestamp(&self) -> DateTime<Local> {
        self.timestamp
    }

    /// Inserts an arbitrary data into the report.
    #[inline(always)]
    pub fn insert<T: Send + Sync + 'static>(&mut self, val: T) {
        self.extensions.insert(val);
    }

    /// Get data inserted in the report via [`Self::insert`].
    ///
    /// Returns `None` if no data with the given type is found.
    #[inline(always)]
    pub fn get<T: Send + Sync + 'static>(&self) -> Option<&T> {
        self.extensions.get()
    }
}

impl eyre::EyreHandler for Report {
    fn debug(&self, error: &(dyn Error + 'static), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Error at {} ({}, {}): ",
            self.location.file(),
            self.location.line(),
            self.location.column()
        )?;

        write!(f, "{error}")?;

        // Causes.
        if error.source().is_some() {
            writeln!(f, "\n\nCaused by:")?;

            let mut curr = error.source();
            let mut idx = 0;
            while let Some(err) = curr {
                writeln!(f, "  {idx}: {err}")?;
                curr = err.source();
                idx += 1;
            }
        }

        // TODO: print backtrace based on backtrace style.
        // TODO(internal): Open-Source Backtrace cleaning solution.
        //
        // Initially, this used to print a cleaned-up version of the
        // backtrace, but the process had very TM-specific filters and was
        // specific to a format that our error reporting infrastructure understood.
        //
        // We'll one day open source it when we've a more general solution to
        // the problem, as this is definitively _extremely_ useful.
        (*self.backtrace()).fmt(f)
    }

    fn track_caller(&mut self, location: &'static Location<'static>) {
        self.location = location;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_report() {
        let rep = Report::default();

        assert_eq!(rep.location().line(), line!() - 2);
        assert_eq!(rep.location().file(), file!());

        std::thread::sleep(std::time::Duration::from_millis(10));

        assert!(rep.timestamp() < Local::now());
        assert!(!rep.backtrace_unresolved().frames().is_empty());

        let symbols_count = rep
            .backtrace()
            .frames()
            .iter()
            .flat_map(|f| f.symbols())
            .count();

        assert!(symbols_count > 0);
    }

    #[test]
    fn test_report_extensions() {
        let mut rep = Report::default();

        rep.insert(2usize);

        assert_eq!(rep.get(), Some(&2usize));

        assert!(rep.get::<String>().is_none());
    }
}
