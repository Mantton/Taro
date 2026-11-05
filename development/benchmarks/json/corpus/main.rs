//! Separate allocation-audit build keeps counting overhead out of timed runs.
use serde::Deserialize;
use serde_json::Value;
use std::{fs, hint::black_box, time::Instant};
#[cfg(feature = "allocation-audit")]
mod audit {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
    pub static COUNT: AtomicU64 = AtomicU64::new(0);
    pub static BYTES: AtomicU64 = AtomicU64::new(0);
    pub struct Allocator;
    unsafe impl GlobalAlloc for Allocator {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            let p = unsafe { System.alloc(l) };
            if !p.is_null() {
                COUNT.fetch_add(1, Relaxed);
                BYTES.fetch_add(l.size() as u64, Relaxed);
            }
            p
        }
        unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
            let p = unsafe { System.alloc_zeroed(l) };
            if !p.is_null() {
                COUNT.fetch_add(1, Relaxed);
                BYTES.fetch_add(l.size() as u64, Relaxed);
            }
            p
        }
        unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
            unsafe { System.dealloc(p, l) }
        }
        unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
            let q = unsafe { System.realloc(p, l, n) };
            if !q.is_null() {
                COUNT.fetch_add(1, Relaxed);
                BYTES.fetch_add(n as u64, Relaxed);
            }
            q
        }
    }
    pub fn snapshot() -> (u64, u64) {
        (COUNT.load(Relaxed), BYTES.load(Relaxed))
    }
}
#[cfg(feature = "allocation-audit")]
#[global_allocator]
static ALLOCATOR: audit::Allocator = audit::Allocator;

#[derive(Deserialize)]
struct Geometry {
    r#type: String,
    coordinates: Vec<Vec<Vec<f64>>>,
}
#[derive(Deserialize)]
struct Properties {
    name: String,
}
#[derive(Deserialize)]
struct Feature {
    r#type: String,
    properties: Properties,
    geometry: Geometry,
}
#[derive(Deserialize)]
struct Canada {
    r#type: String,
    features: Vec<Feature>,
}
#[derive(Default)]
struct Shape {
    objects: u64,
    arrays: u64,
    strings: u64,
    numbers: u64,
    booleans: u64,
    nulls: u64,
    utf8_bytes: u64,
    depth: u64,
}
fn inspect(v: &Value, s: &mut Shape, d: u64) {
    s.depth = s.depth.max(d);
    match v {
        Value::Null => s.nulls += 1,
        Value::Bool(_) => s.booleans += 1,
        Value::Number(_) => s.numbers += 1,
        Value::String(t) => {
            s.strings += 1;
            s.utf8_bytes += t.len() as u64
        }
        Value::Array(a) => {
            s.arrays += 1;
            for v in a {
                inspect(v, s, d + 1)
            }
        }
        Value::Object(a) => {
            s.objects += 1;
            for (k, v) in a {
                s.utf8_bytes += k.len() as u64;
                inspect(v, s, d + 1)
            }
        }
    }
}
fn top(v: &Value) -> u64 {
    match v {
        Value::Array(a) => a.len() as u64,
        Value::Object(a) => a.len() as u64,
        Value::String(a) => a.len() as u64,
        _ => 1,
    }
}
fn operation(input: &str, mode: &str) -> u64 {
    if mode == "dom" {
        let v: Value = serde_json::from_str(black_box(input)).unwrap();
        let n = top(&v);
        black_box(&v);
        n
    } else {
        let v: Canada = serde_json::from_str(black_box(input)).unwrap();
        let n = v.features.len() as u64;
        black_box(&v);
        n
    }
}
fn check(input: &str, mode: &str) {
    if mode == "dom" {
        let v: Value = serde_json::from_str(input).unwrap();
        let mut s = Shape::default();
        inspect(&v, &mut s, 0);
        println!(
            "shape objects={} arrays={} strings={} numbers={} booleans={} nulls={} utf8_bytes={} depth={} top={}",
            s.objects,
            s.arrays,
            s.strings,
            s.numbers,
            s.booleans,
            s.nulls,
            s.utf8_bytes,
            s.depth,
            top(&v)
        );
        return;
    }
    let v: Canada = serde_json::from_str(input).unwrap();
    assert_eq!(v.r#type, "FeatureCollection");
    let (mut rings, mut points, mut coordinates, mut sum) = (0, 0, 0, 0.0);
    for f in &v.features {
        assert_eq!(f.r#type, "Feature");
        assert_eq!(f.properties.name, "Canada");
        assert_eq!(f.geometry.r#type, "Polygon");
        for ring in &f.geometry.coordinates {
            rings += 1;
            for point in ring {
                assert_eq!(point.len(), 2);
                points += 1;
                for x in point {
                    coordinates += 1;
                    sum += x
                }
            }
        }
    }
    println!(
        "typed features={} rings={} points={} coordinates={} float_sum={:.17}",
        v.features.len(),
        rings,
        points,
        coordinates,
        sum
    );
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(
        args.len(),
        6,
        "usage: corpus <check|run|audit> <dom|typed> <file> <count> <samples>"
    );
    let (action, mode) = (&args[1], args[2].as_str());
    assert!(mode == "dom" || mode == "typed");
    let input = fs::read_to_string(&args[3]).unwrap();
    assert!(input.len() <= 100 * 1024 * 1024);
    if action == "check" {
        check(&input, mode);
        return;
    }
    let count: usize = args[4].parse().unwrap();
    let samples: usize = args[5].parse().unwrap();
    assert!(count > 0 && samples > 0 && samples <= 20);
    black_box(operation(&input, mode));
    let mut results = Vec::with_capacity(samples);
    #[cfg(feature = "allocation-audit")]
    let before = audit::snapshot();
    for _ in 0..samples {
        let mut sum = 0;
        let start = Instant::now();
        for _ in 0..count {
            sum += operation(&input, mode)
        }
        let ns = start.elapsed().as_nanos();
        results.push((ns, sum));
    }
    #[cfg(feature = "allocation-audit")]
    let after = audit::snapshot();
    if action == "run" {
        for (ns, sum) in results {
            println!("sample ns={} ops={} checksum={}", ns, count, sum)
        }
    }
    #[cfg(feature = "allocation-audit")]
    println!(
        "stats ops={} allocations={} allocated_bytes={} collections=0",
        count * samples,
        after.0 - before.0,
        after.1 - before.1
    );
    #[cfg(not(feature = "allocation-audit"))]
    println!("stats ops={} collections=0", count * samples);
}
