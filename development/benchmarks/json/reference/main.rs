//! Owned values and output; no borrowed strings, DOMs, or reused output buffers.
use serde::{Deserialize, Serialize};
use std::{
    hint::black_box,
    time::{Duration, Instant},
};

#[derive(Serialize, Deserialize)]
struct Person {
    name: String,
    age: u8,
}

fn measure(mut operation: impl FnMut(), which: &str, bytes: usize) {
    let mut count = 1;
    let elapsed = loop {
        let start = Instant::now();
        for _ in 0..count {
            operation();
        }
        let elapsed = start.elapsed();
        if elapsed >= Duration::from_millis(100) {
            break elapsed;
        }
        count *= 2;
    };
    let target_ns: u64 = std::env::var("JSON_BENCH_SAMPLE_NS")
        .map(|value| value.parse().expect("invalid sample duration"))
        .unwrap_or(50_000_000);
    assert!(target_ns > 0);
    count = ((count as f64 * target_ns as f64 / elapsed.as_nanos() as f64) as usize).max(1);
    let mut samples = Vec::new();
    for _ in 0..20 {
        let start = Instant::now();
        for _ in 0..count {
            operation();
        }
        samples.push(start.elapsed().as_nanos() as f64 / count as f64);
    }
    println!(
        "{}",
        serde_json::json!({"case":which, "samples_ns_per_op":samples,
        "iterations_per_sample":count, "bytes_per_iteration":bytes})
    );
}

fn main() {
    let which = std::env::args().nth(1).expect("expected case");
    let person_input = r#"{"name":"Ada","age":37}"#;
    let array = format!("[{}]", vec![person_input; 128].join(","));
    let input = if which.ends_with("People128") {
        &array
    } else {
        person_input
    };
    if which.ends_with("Person") {
        let value: Person = serde_json::from_str(input).unwrap();
        assert_eq!(value.name, "Ada");
        assert_eq!(value.age, 37);
        assert_eq!(serde_json::to_string(&value).unwrap(), input);
        match which.as_str() {
            "encodePerson" => measure(
                || {
                    black_box(serde_json::to_string(black_box(&value)).unwrap());
                },
                &which,
                input.len(),
            ),
            "decodePerson" => measure(
                || {
                    black_box(serde_json::from_str::<Person>(black_box(input)).unwrap());
                },
                &which,
                input.len(),
            ),
            _ => panic!("unknown case"),
        }
    } else {
        let value: Vec<Person> = serde_json::from_str(input).unwrap();
        assert_eq!(value.len(), 128);
        assert!(value.iter().all(|p| p.name == "Ada" && p.age == 37));
        assert_eq!(serde_json::to_string(&value).unwrap(), input);
        match which.as_str() {
            "encodePeople128" => measure(
                || {
                    black_box(serde_json::to_string(black_box(&value)).unwrap());
                },
                &which,
                input.len(),
            ),
            "decodePeople128" => measure(
                || {
                    black_box(serde_json::from_str::<Vec<Person>>(black_box(input)).unwrap());
                },
                &which,
                input.len(),
            ),
            _ => panic!("unknown case"),
        }
    }
}
