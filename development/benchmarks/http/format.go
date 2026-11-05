// Compare ordinary runtime formatting with format.tr and format.rs.
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"
)

func main() {
	count, err := strconv.Atoi(os.Args[1])
	if err != nil || count <= 0 {
		panic("positive iteration count required")
	}
	var before, after runtime.MemStats
	runtime.ReadMemStats(&before)
	start := time.Now()
	checksum := 0
	for i := 0; i < count; i++ {
		checksum += len(fmt.Sprintf("record %d", i%20))
	}
	elapsed := time.Since(start)
	runtime.ReadMemStats(&after)
	fmt.Printf("checksum=%d bytes=%d allocations=%d collections=%d nanos=%d\n", checksum, after.TotalAlloc-before.TotalAlloc, after.Mallocs-before.Mallocs, after.NumGC-before.NumGC, elapsed.Nanoseconds())
}
