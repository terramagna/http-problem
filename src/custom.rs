pub use http::{StatusCode, Uri};

use super::{CowStr, Extensions, Problem};

/// Define a new custom problem type.
///
/// Although defining a new custom type requires only implementing
/// the [`CustomProblem`] trait, this macro simplifies the code,
/// removing boilerplate from the definition.
///
/// # Example
///
/// ```
/// use http_problem::prelude::{StatusCode, Uri};
/// http_problem::define_custom_type! {
///     /// An error that occurs when a transaction cannot be done
///     /// because one of the accounts doesn't have enough credit.
///     type OutOfCredit {
///         type: "https://example.com/probs/out-of-credit",
///         title: "You do not have enough credit",
///         status: StatusCode::FORBIDDEN,
///         detail(p): format!("You current balance is {}, but that costs {}", p.balance, p.cost),
///         extensions: {
///             balance: i64,
///             cost: i64,
///             accounts: Vec<String>
///         }
///     }
/// }
///
/// fn do_transaction() -> http_problem::Result<()> {
///     Err(OutOfCredit {
///         balance: 50,
///         cost: 30,
///         accounts: vec!["/account/12345".into(), "/account/67890".into()]
///     }.into())
/// }
///
/// fn main() {
///     let problem = do_transaction().unwrap_err();
///     assert_eq!(problem.type_(), &Uri::from_static("https://example.com/probs/out-of-credit"));
///     assert_eq!(problem.title(), "You do not have enough credit");
///     assert_eq!(problem.status(), StatusCode::FORBIDDEN);
///     assert_eq!(problem.details(), "You current balance is 50, but that costs 30");
///     assert_eq!(problem.extensions().len(), 3);
/// }
/// ```
#[macro_export]
macro_rules! define_custom_type {
	($(#[$meta: meta])* type $rstyp: ident {
        type: $typ:literal,
        title: $title:literal,
        status: $status: expr,
        detail($prob: ident): $detail: expr,
        extensions: {
            $($field:ident: $field_ty: ty),* $(,)?
        } $(,)?
    }) => {
        $(#[$meta])*
        #[derive(Debug)]
        pub struct $rstyp {
            $(pub $field: $field_ty),*
        }

        impl ::std::fmt::Display for $rstyp {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                writeln!(f, "{}", <Self as $crate::prelude::CustomProblem>::details(self))
            }
        }

        impl ::std::error::Error for $rstyp {}

        impl $crate::prelude::CustomProblem for $rstyp {
            fn problem_type(&self) -> $crate::prelude::Uri {
                $crate::prelude::Uri::from_static($typ)
            }

            fn title(&self) -> &'static str {
                $title
            }

            fn status_code(&self) -> $crate::prelude::StatusCode {
                $status
            }

            fn details(&self) -> $crate::CowStr {
                let $prob = self;
                $detail.into()
            }

            fn add_extensions(
                &self,
                _extensions: &mut $crate::Extensions)
            {
                $(
                    _extensions.insert(stringify!($field), &self.$field);
                )*
            }
        }
	};
}

/// A trait defining custom problem types.
///
/// Implementing this trait provides enough information to create a
/// [`Problem`] instance with the correct values for each field.
///
/// There is no need to implement `From<Self> for Problem` if you
/// implement this trait.
///
/// See [`define_custom_type!`] for a convenient way of implementing
/// this trait.
pub trait CustomProblem: std::error::Error + Send + Sync + 'static {
    /// A URI reference that identifies the problem type.
    ///
    /// See [`Problem::type_`] more information.
    fn problem_type(&self) -> Uri;

    /// A short, human-readable summary of the problem type.
    ///
    /// See [`Problem::title`] for more information.
    fn title(&self) -> &'static str;

    /// The HTTP status code for this problem type.
    ///
    /// See [`Problem::status`] for more information.
    fn status_code(&self) -> StatusCode;

    /// A human-readable explanation of the occurrence.
    ///
    /// See [`Problem::details`] for more information.
    fn details(&self) -> CowStr;

    /// Add extensions to the final problem instance.
    ///
    /// See [`Problem::with_extension`] for more info.
    fn add_extensions(&self, extensions: &mut Extensions);
}

impl<C: CustomProblem> From<C> for Problem {
    #[track_caller]
    fn from(custom: C) -> Self {
        let mut problem = Self::custom(custom.status_code(), custom.problem_type())
            .with_title(custom.title())
            .with_detail(custom.details());

        custom.add_extensions(problem.extensions_mut());

        problem.with_cause(custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    define_custom_type! {
        /// An error that occurs when a transaction cannot be done
        /// because one of the accounts doesn't have enough credit.
        type OutOfCredit {
            type: "https://example.com/probs/out-of-credit",
            title: "You do not have enough credit",
            status: StatusCode::FORBIDDEN,
            detail(p): format!("You current balance is {}, but that costs {}", p.balance, p.cost),
            extensions: {
                balance: i64,
                cost: i64,
                accounts: Vec<String>
            }
        }
    }

    #[test]
    fn test_macro_output() {
        let error = OutOfCredit {
            balance: 30,
            cost: 50,
            accounts: vec!["aaa".into(), "bbb".into()],
        };

        assert_eq!(error.title(), "You do not have enough credit");
        assert_eq!(error.status_code(), StatusCode::FORBIDDEN);
        assert_eq!(
            error.details(),
            "You current balance is 30, but that costs 50"
        );
    }

    #[test]
    fn test_custom_problem_to_problem() {
        let error = OutOfCredit {
            balance: 30,
            cost: 50,
            accounts: vec!["aaa".into(), "bbb".into()],
        };

        let prob: Problem = error.into();

        assert_eq!(prob.title(), "You do not have enough credit");
        assert_eq!(prob.status(), StatusCode::FORBIDDEN);
        assert_eq!(
            prob.details(),
            "You current balance is 30, but that costs 50"
        );
    }
}
