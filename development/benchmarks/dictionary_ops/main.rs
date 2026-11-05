// Keep operation boundaries and checksums aligned with main.tr and main.go.
use std::{collections::HashMap, hint::black_box, time::Instant};
#[derive(Clone, Copy)]
struct Value {
    kind: i64,
    payload: i64,
}
type Map = HashMap<&'static str, Value>;

#[inline(never)]
fn make_dictionary() -> Map {
    black_box(Map::new())
}
#[inline(never)]
fn observe(m: &Map) -> i64 {
    black_box(m).len() as i64
}
#[inline(never)]
fn put(m: &mut Map, key: &'static str, payload: i64) {
    m.insert(key, Value { kind: 1, payload });
}
#[inline(never)]
fn get(m: &Map, key: &str) -> i64 {
    // Prevent LLVM from hoisting identical miss lookups out of the loop.
    match black_box(m).get(black_box(key)) {
        Some(v) => v.kind + v.payload,
        None => -1,
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(
        args.len(),
        4,
        "usage: dictionary_ops <case> <iterations> <entries: 1|16>"
    );
    let name = args[1].as_str();
    let count: i64 = args[2].parse().unwrap();
    let entries: i64 = args[3].parse().unwrap();
    assert!(count > 0 && (entries == 1 || entries == 16));
    let keys = [
        "x",
        "fibonacci",
        "alpha",
        "bravo",
        "charlie",
        "delta",
        "echo",
        "foxtrot",
        "golf",
        "hotel",
        "india",
        "juliet",
        "kilo",
        "lima",
        "mike",
        "november",
    ];
    let mut checksum: i64 = 0;
    let mut elapsed: u128 = 0;
    if name == "first_insert" || name == "insert_new" {
        let target = if name == "first_insert" {
            keys[0]
        } else {
            "new_binding"
        };
        let mut done = 0;
        while done < count {
            let batch = (count - done).min(1024);
            let mut maps: Vec<_> = (0..batch).map(|_| make_dictionary()).collect();
            if name == "insert_new" {
                for m in &mut maps {
                    for k in 0..entries {
                        put(m, keys[k as usize], k);
                    }
                }
            }
            let start = Instant::now();
            for (j, m) in maps.iter_mut().enumerate() {
                put(m, target, done + j as i64);
            }
            elapsed += start.elapsed().as_nanos();
            for m in &maps {
                checksum += get(m, target);
            }
            done += batch;
        }
    } else if name == "construct" || name == "construct_insert" {
        let populate = name == "construct_insert";
        let start = Instant::now();
        for i in 0..count {
            let mut m = make_dictionary();
            if populate {
                put(&mut m, keys[0], i);
            }
            checksum += observe(&m);
        }
        elapsed = start.elapsed().as_nanos();
    } else {
        let mut m = make_dictionary();
        for j in 0..entries {
            put(&mut m, keys[j as usize], j);
        }
        let start = Instant::now();
        match name {
            "overwrite" => {
                for i in 0..count {
                    put(&mut m, keys[(i % entries) as usize], i);
                }
            }
            "hit" => {
                for i in 0..count {
                    checksum += get(&m, keys[(i % entries) as usize]);
                }
            }
            "miss" => {
                for _ in 0..count {
                    checksum += get(&m, "absent");
                }
            }
            _ => panic!("unknown case"),
        }
        elapsed = start.elapsed().as_nanos();
        if name == "overwrite" {
            for j in 0..entries {
                checksum += get(&m, keys[j as usize]);
            }
        }
    }
    println!("benchmark case={name} iterations={count} entries={entries} elapsed_ns={elapsed} checksum={checksum}");
}
