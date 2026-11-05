// Fresh full DOMs or the complete Canada fixture model; file I/O is untimed.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"
)

const maxBytes = 100 * 1024 * 1024

type Geometry struct {
	Type        string        `json:"type"`
	Coordinates [][][]float64 `json:"coordinates"`
}
type Properties struct {
	Name string `json:"name"`
}
type Feature struct {
	Type       string     `json:"type"`
	Properties Properties `json:"properties"`
	Geometry   Geometry   `json:"geometry"`
}
type Canada struct {
	Type     string    `json:"type"`
	Features []Feature `json:"features"`
}
type Shape struct{ objects, arrays, strings, numbers, booleans, nulls, utf8_bytes, depth uint64 }

func inspect(v any, s *Shape, d uint64) {
	if d > s.depth {
		s.depth = d
	}
	switch x := v.(type) {
	case nil:
		s.nulls++
	case bool:
		s.booleans++
	case float64:
		s.numbers++
	case string:
		s.strings++
		s.utf8_bytes += uint64(len(x))
	case []any:
		s.arrays++
		for _, child := range x {
			inspect(child, s, d+1)
		}
	case map[string]any:
		s.objects++
		for k, child := range x {
			s.utf8_bytes += uint64(len(k))
			inspect(child, s, d+1)
		}
	default:
		panic("unknown DOM value")
	}
}
func top(v any) uint64 {
	switch x := v.(type) {
	case []any:
		return uint64(len(x))
	case map[string]any:
		return uint64(len(x))
	case string:
		return uint64(len(x))
	default:
		return 1
	}
}
func require(err error) {
	if err != nil {
		panic(err)
	}
}
func operation(input []byte, mode string) uint64 {
	if mode == "dom" {
		var v any
		require(json.Unmarshal(input, &v))
		n := top(v)
		runtime.KeepAlive(v)
		return n
	}
	var v Canada
	require(json.Unmarshal(input, &v))
	n := uint64(len(v.Features))
	runtime.KeepAlive(v)
	return n
}
func check(input []byte, mode string) {
	if mode == "dom" {
		var v any
		require(json.Unmarshal(input, &v))
		runtime.GC()
		s := Shape{}
		inspect(v, &s, 0)
		fmt.Printf("shape objects=%d arrays=%d strings=%d numbers=%d booleans=%d nulls=%d utf8_bytes=%d depth=%d top=%d\n", s.objects, s.arrays, s.strings, s.numbers, s.booleans, s.nulls, s.utf8_bytes, s.depth, top(v))
		return
	}
	var v Canada
	require(json.Unmarshal(input, &v))
	runtime.GC()
	if v.Type != "FeatureCollection" {
		panic("root type")
	}
	rings, points, coordinates := 0, 0, 0
	sum := 0.0
	for _, f := range v.Features {
		if f.Type != "Feature" || f.Properties.Name != "Canada" || f.Geometry.Type != "Polygon" {
			panic("feature fields")
		}
		for _, ring := range f.Geometry.Coordinates {
			rings++
			for _, p := range ring {
				if len(p) != 2 {
					panic("point dimension")
				}
				points++
				for _, x := range p {
					coordinates++
					sum += x
				}
			}
		}
	}
	fmt.Printf("typed features=%d rings=%d points=%d coordinates=%d float_sum=%.17g\n", len(v.Features), rings, points, coordinates, sum)
}
func main() {
	if len(os.Args) != 6 {
		panic("usage: corpus <check|run|audit> <dom|typed> <file> <count> <samples>")
	}
	action, mode := os.Args[1], os.Args[2]
	if mode != "dom" && mode != "typed" {
		panic("unknown mode")
	}
	input, err := os.ReadFile(os.Args[3])
	require(err)
	if len(input) > maxBytes {
		panic("input exceeds 100 MiB")
	}
	if action == "check" {
		check(input, mode)
		return
	}
	count, err := strconv.Atoi(os.Args[4])
	require(err)
	samples, err := strconv.Atoi(os.Args[5])
	require(err)
	if count < 1 || samples < 1 || samples > 20 {
		panic("invalid counts")
	}
	operation(input, mode)
	runtime.GC()
	times := make([]int64, samples)
	checksums := make([]uint64, samples)
	var before, after runtime.MemStats
	runtime.ReadMemStats(&before)
	for sample := 0; sample < samples; sample++ {
		sum := uint64(0)
		start := time.Now()
		for i := 0; i < count; i++ {
			sum += operation(input, mode)
		}
		times[sample] = time.Since(start).Nanoseconds()
		checksums[sample] = sum
	}
	runtime.ReadMemStats(&after)
	if action == "run" {
		for i, ns := range times {
			fmt.Printf("sample ns=%d ops=%d checksum=%d\n", ns, count, checksums[i])
		}
	}
	fmt.Printf("stats ops=%d allocations=%d allocated_bytes=%d collections=%d pause_ns=%d heap_bytes=%d\n", count*samples, after.Mallocs-before.Mallocs, after.TotalAlloc-before.TotalAlloc, after.NumGC-before.NumGC, after.PauseTotalNs-before.PauseTotalNs, after.HeapAlloc)
}
