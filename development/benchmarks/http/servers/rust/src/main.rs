use axum::{Json, Router, http::header, routing::get};
use serde::Serialize;

#[derive(Serialize)]
struct Message {
    message: &'static str,
}
async fn text() -> &'static str {
    "Hello, World!"
}
async fn json() -> Json<Message> {
    Json(Message {
        message: "Hello, World!",
    })
}
#[derive(Serialize)]
struct Record {
    id: i32,
    message: String,
}
const RECORDS_JSON: &str = "[{\"id\":0,\"message\":\"record 0\"},{\"id\":1,\"message\":\"record 1\"},{\"id\":2,\"message\":\"record 2\"},{\"id\":3,\"message\":\"record 3\"},{\"id\":4,\"message\":\"record 4\"},{\"id\":5,\"message\":\"record 5\"},{\"id\":6,\"message\":\"record 6\"},{\"id\":7,\"message\":\"record 7\"},{\"id\":8,\"message\":\"record 8\"},{\"id\":9,\"message\":\"record 9\"},{\"id\":10,\"message\":\"record 10\"},{\"id\":11,\"message\":\"record 11\"},{\"id\":12,\"message\":\"record 12\"},{\"id\":13,\"message\":\"record 13\"},{\"id\":14,\"message\":\"record 14\"},{\"id\":15,\"message\":\"record 15\"},{\"id\":16,\"message\":\"record 16\"},{\"id\":17,\"message\":\"record 17\"},{\"id\":18,\"message\":\"record 18\"},{\"id\":19,\"message\":\"record 19\"}]";
fn encode_records() -> Json<Vec<Record>> {
    Json(
        (0..20)
            .map(|id| Record {
                id,
                message: format!("record {id}"),
            })
            .collect(),
    )
}
async fn stage_static() -> ([(header::HeaderName, &'static str); 1], &'static str) {
    ([(header::CONTENT_TYPE, "application/json")], RECORDS_JSON)
}
async fn stage_sleep() -> ([(header::HeaderName, &'static str); 1], &'static str) {
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;
    stage_static().await
}
async fn stage_encode() -> Json<Vec<Record>> {
    encode_records()
}
async fn app() -> Json<Vec<Record>> {
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;
    encode_records()
}
async fn json_static() -> ([(header::HeaderName, &'static str); 1], &'static str) {
    (
        [(header::CONTENT_TYPE, "application/json")],
        r#"{"message":"Hello, World!"}"#,
    )
}
fn main() {
    let port: u16 = std::env::args().nth(1).unwrap().parse().unwrap();
    let workers: usize = std::env::var("BENCH_WORKERS").unwrap().parse().unwrap();
    let host = std::env::var("BENCH_HOST").unwrap_or_else(|_| "127.0.0.1".into());
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(workers)
        .enable_all()
        .build()
        .unwrap()
        .block_on(async {
            let router = Router::new()
                .route("/text", get(text))
                .route("/json", get(json))
                .route("/json-static", get(json_static))
                .route("/app", get(app))
                .route("/stage/static", get(stage_static))
                .route("/stage/sleep", get(stage_sleep))
                .route("/stage/encode", get(stage_encode));
            let listener = tokio::net::TcpListener::bind((host.as_str(), port))
                .await
                .unwrap();
            axum::serve(listener, router).await.unwrap();
        });
}
