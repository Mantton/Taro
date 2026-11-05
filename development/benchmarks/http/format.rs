// Compare ordinary format! with format.tr and format.go; no custom allocator.
fn main() {
    let count: usize = std::env::args().nth(1).unwrap().parse().unwrap();
    assert!(count > 0);
    let start = std::time::Instant::now();
    let mut checksum = 0;
    for index in 0..count {
        let label = format!("record {}", std::hint::black_box(index % 20));
        checksum += label.len();
    }
    println!("checksum={checksum} nanos={}", start.elapsed().as_nanos());
}
