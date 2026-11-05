// Reference for the typed record cases in ../src/records.tr.
package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"runtime"
	"runtime/pprof"
	"strconv"
	"time"
)

type Person struct {
	Name string `json:"name"`
	Age  uint8  `json:"age"`
}

var personSink Person
var peopleSink []Person
var bytesSink []byte

func main() {
	if len(os.Args) != 2 {
		panic("expected encodePerson, decodePerson, encodePeople128 or decodePeople128")
	}
	which := os.Args[1]
	input := []byte(`{"name":"Ada","age":37}`)
	if which == "encodePeople128" || which == "decodePeople128" {
		records := make([][]byte, 128)
		for i := range records {
			records[i] = input
		}
		input = append(append([]byte{'['}, bytes.Join(records, []byte{','})...), ']')
	}
	var person Person
	var people []Person
	var operation func()
	check := func(err error) {
		if err != nil {
			panic(err)
		}
	}
	if which == "encodePerson" || which == "decodePerson" {
		check(json.Unmarshal(input, &person))
		if person.Name != "Ada" || person.Age != 37 {
			panic("record mismatch")
		}
		encoded, err := json.Marshal(&person)
		check(err)
		if !bytes.Equal(input, encoded) {
			panic("round trip mismatch")
		}
	} else {
		check(json.Unmarshal(input, &people))
		if len(people) != 128 {
			panic("record count mismatch")
		}
		for _, p := range people {
			if p.Name != "Ada" || p.Age != 37 {
				panic("record mismatch")
			}
		}
		encoded, err := json.Marshal(&people)
		check(err)
		if !bytes.Equal(input, encoded) {
			panic("round trip mismatch")
		}
	}
	switch which {
	case "decodePerson":
		operation = func() { var value Person; check(json.Unmarshal(input, &value)); personSink = value }
	case "decodePeople128":
		operation = func() { var value []Person; check(json.Unmarshal(input, &value)); peopleSink = value }
	case "encodePerson":
		operation = func() { var err error; bytesSink, err = json.Marshal(&person); check(err) }
	case "encodePeople128":
		operation = func() { var err error; bytesSink, err = json.Marshal(&people); check(err) }
	default:
		panic("unknown case")
	}
	count := 1
	var elapsed time.Duration
	for {
		start := time.Now()
		for i := 0; i < count; i++ {
			operation()
		}
		elapsed = time.Since(start)
		if elapsed >= 100*time.Millisecond {
			break
		}
		count *= 2
	}
	target := 50 * time.Millisecond
	if raw := os.Getenv("JSON_BENCH_SAMPLE_NS"); raw != "" {
		nanos, err := strconv.ParseInt(raw, 10, 64)
		check(err)
		if nanos <= 0 {
			panic("JSON_BENCH_SAMPLE_NS must be positive")
		}
		target = time.Duration(nanos)
	}
	count = max(1, int(float64(count)*float64(target)/float64(elapsed)))
	if path := os.Getenv("JSON_BENCH_CPU_PROFILE"); path != "" {
		file, err := os.Create(path)
		check(err)
		defer file.Close()
		check(pprof.StartCPUProfile(file))
		defer pprof.StopCPUProfile()
	}
	samples := make([]float64, 20)
	for sample := range samples {
		start := time.Now()
		for i := 0; i < count; i++ {
			operation()
		}
		samples[sample] = float64(time.Since(start).Nanoseconds()) / float64(count)
	}
	runtime.KeepAlive(input)
	output, err := json.Marshal(map[string]any{"case": which, "samples_ns_per_op": samples, "iterations_per_sample": count, "bytes_per_iteration": len(input)})
	check(err)
	fmt.Println(string(output))
}
