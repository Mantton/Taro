// Keep operation boundaries and checksums aligned with main.tr and main.rs.
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"
)

type value struct{ kind, payload int64 }

//go:noinline
func makeDictionary() map[string]value { return make(map[string]value) }

//go:noinline
func observe(m map[string]value) int64 { runtime.KeepAlive(m); return int64(len(m)) }

//go:noinline
func put(m map[string]value, key string, payload int64) { m[key] = value{1, payload} }

//go:noinline
func get(m map[string]value, key string) int64 {
	if v, ok := m[key]; ok {
		return v.kind + v.payload
	}
	return -1
}

func main() {
	if len(os.Args) != 4 {
		panic("usage: dictionary_ops <case> <iterations> <entries: 1|16>")
	}
	name := os.Args[1]
	count, err := strconv.ParseInt(os.Args[2], 10, 64)
	if err != nil || count < 1 {
		panic("invalid count")
	}
	entries, err := strconv.ParseInt(os.Args[3], 10, 64)
	if err != nil || (entries != 1 && entries != 16) {
		panic("invalid entries")
	}
	keys := []string{"x", "fibonacci", "alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel", "india", "juliet", "kilo", "lima", "mike", "november"}
	var checksum, elapsed int64
	if name == "first_insert" || name == "insert_new" {
		target := keys[0]
		if name == "insert_new" {
			target = "new_binding"
		}
		for done := int64(0); done < count; {
			batch := min(count-done, 1024)
			maps := make([]map[string]value, batch)
			for j := range maps {
				maps[j] = makeDictionary()
				if name == "insert_new" {
					for k := int64(0); k < entries; k++ {
						put(maps[j], keys[k], k)
					}
				}
			}
			start := time.Now()
			for j, m := range maps {
				put(m, target, done+int64(j))
			}
			elapsed += time.Since(start).Nanoseconds()
			for _, m := range maps {
				checksum += get(m, target)
			}
			done += batch
		}
	} else if name == "construct" || name == "construct_insert" {
		populate := name == "construct_insert"
		start := time.Now()
		for i := int64(0); i < count; i++ {
			m := makeDictionary()
			if populate {
				put(m, keys[0], i)
			}
			checksum += observe(m)
		}
		elapsed = time.Since(start).Nanoseconds()
	} else {
		m := makeDictionary()
		for j := int64(0); j < entries; j++ {
			put(m, keys[j], j)
		}
		start := time.Now()
		switch name {
		case "overwrite":
			for i := int64(0); i < count; i++ {
				put(m, keys[i%entries], i)
			}
		case "hit":
			for i := int64(0); i < count; i++ {
				checksum += get(m, keys[i%entries])
			}
		case "miss":
			for i := int64(0); i < count; i++ {
				checksum += get(m, "absent")
			}
		default:
			panic("unknown case")
		}
		elapsed = time.Since(start).Nanoseconds()
		if name == "overwrite" {
			for j := int64(0); j < entries; j++ {
				checksum += get(m, keys[j])
			}
		}
		runtime.KeepAlive(m)
	}
	fmt.Printf("benchmark case=%s iterations=%d entries=%d elapsed_ns=%d checksum=%d\n", name, count, entries, elapsed, checksum)
}
