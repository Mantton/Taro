package main

import (
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"runtime"
	"time"
)

type Record struct {
	ID      int    `json:"id"`
	Message string `json:"message"`
}

type Message struct {
	Message string `json:"message"`
}

const recordsJSON = `[{"id":0,"message":"record 0"},{"id":1,"message":"record 1"},{"id":2,"message":"record 2"},{"id":3,"message":"record 3"},{"id":4,"message":"record 4"},{"id":5,"message":"record 5"},{"id":6,"message":"record 6"},{"id":7,"message":"record 7"},{"id":8,"message":"record 8"},{"id":9,"message":"record 9"},{"id":10,"message":"record 10"},{"id":11,"message":"record 11"},{"id":12,"message":"record 12"},{"id":13,"message":"record 13"},{"id":14,"message":"record 14"},{"id":15,"message":"record 15"},{"id":16,"message":"record 16"},{"id":17,"message":"record 17"},{"id":18,"message":"record 18"},{"id":19,"message":"record 19"}]`

func encodeRecords() []byte {
	records := make([]Record, 0, 20)
	for id := 0; id < 20; id++ {
		records = append(records, Record{id, fmt.Sprintf("record %d", id)})
	}
	data, err := json.Marshal(records)
	if err != nil {
		panic(err)
	}
	return data
}
func writeRecords(w http.ResponseWriter, data []byte) {
	w.Header().Set("Content-Type", "application/json")
	_, _ = w.Write(data)
}

func main() {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /text", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		_, _ = w.Write([]byte("Hello, World!"))
	})
	mux.HandleFunc("GET /json", func(w http.ResponseWriter, r *http.Request) {
		data, err := json.Marshal(Message{Message: "Hello, World!"})
		if err != nil {
			http.Error(w, "encoding failed", 500)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_, _ = w.Write(data)
	})
	mux.HandleFunc("GET /json-static", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_, _ = w.Write([]byte(`{"message":"Hello, World!"}`))
	})
	mux.HandleFunc("GET /stage/static", func(w http.ResponseWriter, r *http.Request) {
		writeRecords(w, []byte(recordsJSON))
	})
	mux.HandleFunc("GET /stage/sleep", func(w http.ResponseWriter, r *http.Request) {
		time.Sleep(time.Millisecond)
		writeRecords(w, []byte(recordsJSON))
	})
	mux.HandleFunc("GET /stage/encode", func(w http.ResponseWriter, r *http.Request) {
		writeRecords(w, encodeRecords())
	})
	mux.HandleFunc("GET /app", func(w http.ResponseWriter, r *http.Request) {
		time.Sleep(time.Millisecond)
		writeRecords(w, encodeRecords())
	})
	mux.HandleFunc("GET /stats", func(w http.ResponseWriter, r *http.Request) {
		var stats runtime.MemStats
		runtime.ReadMemStats(&stats)
		data, _ := json.Marshal(struct {
			Allocations    uint64 `json:"allocations"`
			AllocatedBytes uint64 `json:"allocatedBytes"`
			Collections    uint32 `json:"collections"`
			PauseNanos     uint64 `json:"pauseNanos"`
		}{stats.Mallocs, stats.TotalAlloc, stats.NumGC, stats.PauseTotalNs})
		w.Header().Set("Content-Type", "application/json")
		_, _ = w.Write(data)
	})
	host := os.Getenv("BENCH_HOST")
	if host == "" {
		host = "127.0.0.1"
	}
	// Diagnostic control: plain net/http has no per-handler deadline.
	var handler http.Handler = mux
	if os.Getenv("BENCH_HANDLER_TIMEOUT") == "1" {
		handler = http.TimeoutHandler(mux, 30*time.Second, "timeout")
	}
	server := &http.Server{Addr: host + ":" + os.Args[1], Handler: handler, ReadHeaderTimeout: 30 * time.Second, IdleTimeout: 30 * time.Second}
	if err := server.ListenAndServe(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
