use actix_web::{
    http::{header, StatusCode},
    Either, HttpResponse, ResponseError,
};

use crate::{http, CowStr, Problem, Result};

impl ResponseError for Problem {
    fn status_code(&self) -> StatusCode {
        StatusCode::from_u16(self.status().as_u16()).expect("status is valid")
    }

    fn error_response(&self) -> HttpResponse {
        self.report_as_error();

        HttpResponse::build(self.status_code())
            .insert_header((header::CONTENT_TYPE, "application/problem+json"))
            .json(self)
    }
}

/// Extension trait for actix-web's `Either` type, which provide additional
/// methods for a more ergonomic error handling.
pub trait EitherExt<L, R> {
    /// Returns a result with the value of the `Left` variant.
    ///
    /// # Errors
    ///
    /// Returns a `BadRequest` (with the provided message) if the container
    /// doesn't hold a `Left`.
    fn try_left(self, msg: impl Into<CowStr>) -> Result<L>;
    /// Returns a result with the value of the `Right` variant.
    ///
    /// # Errors
    ///
    /// Returns a `BadRequest` (with the provided message) if the container
    /// doesn't hold a `Right`.
    fn try_right(self, msg: impl Into<CowStr>) -> Result<R>;
}

impl<L, R> EitherExt<L, R> for Either<L, R> {
    #[track_caller]
    fn try_left(self, msg: impl Into<CowStr>) -> Result<L> {
        match self {
            Either::Left(val) => Ok(val),
            Either::Right(_) => Err(http::bad_request(msg)),
        }
    }

    #[track_caller]
    fn try_right(self, msg: impl Into<CowStr>) -> Result<R> {
        match self {
            Either::Left(_) => Err(http::bad_request(msg)),
            Either::Right(val) => Ok(val),
        }
    }
}

#[cfg(test)]
mod tests {
    use actix_web::body::MessageBody;

    use super::*;

    #[test]
    fn test_response_error() {
        let err = crate::http::failed_precondition();

        let actix_status = ::http::StatusCode::from_u16(err.status_code().as_u16()).unwrap();
        assert_eq!(actix_status, err.status());

        let resp = err.error_response();
        let actix_status = ::http::StatusCode::from_u16(resp.status().as_u16()).unwrap();
        assert_eq!(actix_status, err.status());
        assert_eq!(
            resp.headers().get(header::CONTENT_TYPE).unwrap().as_bytes(),
            b"application/problem+json"
        );

        let body = resp.into_body().try_into_bytes().unwrap();

        assert_eq!(body, serde_json::to_vec(&err).unwrap());
    }

    #[test]
    fn try_left_works() {
        let a = Either::<i32, i32>::Left(1);
        assert_eq!(1, a.try_left("a err").unwrap());

        let b = Either::<i32, i32>::Right(2);
        let err = b.try_left("b err").unwrap_err();
        assert!(err.is::<http::BadRequest>());
        assert_eq!("b err", err.details());
    }

    #[test]
    fn try_right_works() {
        let a = Either::<i32, i32>::Left(1);
        let err = a.try_right("a err").unwrap_err();
        assert!(err.is::<http::BadRequest>());
        assert_eq!("a err", err.details());

        let b = Either::<i32, i32>::Right(2);
        assert_eq!(2, b.try_right("b err").unwrap());
    }
}
