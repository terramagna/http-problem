use axum::{
    http::header,
    response::{IntoResponse, Json, Response},
};

use crate::Problem;

impl IntoResponse for Problem {
    fn into_response(self) -> Response {
        self.report_as_error();

        (
            self.status(),
            [(header::CONTENT_TYPE, "application/problem+json")],
            Json(&self),
        )
            .into_response()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_into_response() {
        let err = crate::http::failed_precondition();

        let resp = crate::http::failed_precondition().into_response();

        assert_eq!(resp.status(), err.status());
        assert_eq!(
            resp.headers().get(header::CONTENT_TYPE).unwrap().as_bytes(),
            b"application/problem+json"
        );
    }
}
