// The workload shapes in this file intentionally match host_gap.tr. Keep
// escaping/noinline boundaries synchronized when changing either fixture.
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"
)

type benchValue struct {
	kind    int64
	payload int64
}

type benchScope struct {
	values map[string]benchValue
	outer  *benchScope
}

func newScope() benchScope {
	return benchScope{values: make(map[string]benchValue)}
}

func enclosedScope(outer *benchScope) benchScope {
	return benchScope{values: make(map[string]benchValue), outer: outer}
}

func (scope *benchScope) define(name string, value benchValue) {
	scope.values[name] = value
}

//go:noinline
func (scope *benchScope) lookup(name string) (benchValue, bool) {
	if value, ok := scope.values[name]; ok {
		return value, true
	}
	if scope.outer != nil {
		return scope.outer.lookup(name)
	}
	return benchValue{}, false
}

//go:noinline
func boxScope(scope benchScope) *benchScope {
	return &scope
}

//go:noinline
func makeChildScope(outer *benchScope, value int64) *benchScope {
	child := boxScope(enclosedScope(outer))
	child.define("x", benchValue{kind: 1, payload: value})
	return child
}

func requireValue(value benchValue, ok bool) benchValue {
	if !ok {
		panic("benchmark lookup unexpectedly missed")
	}
	return value
}

func environmentChurn(iterations int64) int64 {
	root := boxScope(newScope())
	root.define("fibonacci", benchValue{kind: 7, payload: 11})

	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		child := makeChildScope(root, iteration)
		local := requireValue(child.lookup("x"))
		outer := requireValue(child.lookup("fibonacci"))
		checksum += local.kind + local.payload + outer.kind + outer.payload
		runtime.KeepAlive(child)
	}
	runtime.KeepAlive(root)
	return checksum
}

func environmentLookup(iterations int64) int64 {
	root := boxScope(newScope())
	root.define("fibonacci", benchValue{kind: 7, payload: 11})
	child := makeChildScope(root, 23)

	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		local := requireValue(child.lookup("x"))
		outer := requireValue(child.lookup("fibonacci"))
		checksum += local.kind + local.payload + outer.kind + outer.payload
	}
	runtime.KeepAlive(child)
	runtime.KeepAlive(root)
	return checksum
}

func dictionaryLookup(iterations int64) int64 {
	values := make(map[string]benchValue)
	values["fibonacci"] = benchValue{kind: 7, payload: 11}
	key := "fibonacci"

	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		value, ok := values[key]
		if !ok {
			panic("benchmark dictionary lookup unexpectedly missed")
		}
		checksum += value.kind + value.payload
	}
	runtime.KeepAlive(values)
	return checksum
}

//go:noinline
func buildArguments(value int64) []benchValue {
	arguments := []benchValue{}
	arguments = append(arguments, benchValue{kind: 1, payload: value})
	arguments = append(arguments, benchValue{kind: 1, payload: value + 1})
	return arguments
}

//go:noinline
func consumeArguments(arguments []benchValue) int64 {
	return arguments[0].payload + arguments[1].payload
}

func argumentList(iterations int64) int64 {
	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		arguments := buildArguments(iteration)
		checksum += consumeArguments(arguments)
	}
	return checksum
}

type benchError int64

func (err benchError) Error() string {
	return "negative benchmark input"
}

var negativeInput error = benchError(-1)

//go:noinline
func resultLeaf(value int64) (int64, error) {
	if value < 0 {
		return 0, negativeInput
	}
	return value + 1, nil
}

//go:noinline
func resultMiddle(value int64) (int64, error) {
	next, err := resultLeaf(value)
	if err != nil {
		return 0, err
	}
	return next * 3, nil
}

//go:noinline
func resultTop(value int64) (int64, error) {
	next, err := resultMiddle(value)
	if err != nil {
		return 0, err
	}
	return next - 2, nil
}

func resultSuccess(iterations int64) int64 {
	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		value, err := resultTop(iteration)
		if err != nil {
			panic("success benchmark returned an error")
		}
		checksum += value
	}
	return checksum
}

type benchNode struct {
	value int64
}

//go:noinline
func makeNode(value int64) *benchNode {
	return &benchNode{value: value}
}

func smallAllocation(iterations int64) int64 {
	var checksum int64
	for iteration := int64(0); iteration < iterations; iteration++ {
		node := makeNode(iteration)
		checksum += node.value
		runtime.KeepAlive(node)
	}
	return checksum
}

type workload func(int64) int64

func selectWorkload(name string) workload {
	switch name {
	case "dictionary_lookup":
		return dictionaryLookup
	case "environment_churn":
		return environmentChurn
	case "environment_lookup":
		return environmentLookup
	case "argument_list":
		return argumentList
	case "result_success":
		return resultSuccess
	case "small_allocation":
		return smallAllocation
	default:
		return nil
	}
}

func usage() {
	fmt.Fprintln(os.Stderr, "usage: host_gap <case> <positive-iterations>")
}

func main() {
	if len(os.Args) != 3 {
		usage()
		os.Exit(2)
	}

	caseName := os.Args[1]
	selected := selectWorkload(caseName)
	if selected == nil {
		fmt.Fprintf(os.Stderr, "unknown benchmark case: %s\n", caseName)
		usage()
		os.Exit(2)
	}

	iterations, err := strconv.ParseInt(os.Args[2], 10, 64)
	if err != nil || iterations < 1 {
		usage()
		os.Exit(2)
	}

	// Exclude fixture startup and any previous process work from Go's counters.
	runtime.GC()
	var before runtime.MemStats
	runtime.ReadMemStats(&before)
	started := time.Now()
	checksum := selected(iterations)
	elapsed := time.Since(started)
	var after runtime.MemStats
	runtime.ReadMemStats(&after)

	fmt.Printf(
		"benchmark case=%s iterations=%d elapsed_ns=%d checksum=%d\n",
		caseName,
		iterations,
		elapsed.Nanoseconds(),
		checksum,
	)
	fmt.Fprintf(
		os.Stderr,
		"go stats: collections=%d allocations=%d allocated_bytes=%d\n",
		after.NumGC-before.NumGC,
		after.Mallocs-before.Mallocs,
		after.TotalAlloc-before.TotalAlloc,
	)
}
