-- No per-response Lua hook: payload/Content-Type correctness is validated
-- separately before/after timing, preserving load-generator headroom.
function done(summary, latency, requests)
  io.write(string.format("{\"requests\":%d,\"duration_us\":%d,\"bytes\":%d,\"p50_us\":%.3f,\"p95_us\":%.3f,\"p99_us\":%.3f,\"connect_errors\":%d,\"read_errors\":%d,\"write_errors\":%d,\"status_errors\":%d,\"timeouts\":%d}\n",
    summary.requests, summary.duration, summary.bytes,
    latency:percentile(50), latency:percentile(95), latency:percentile(99),
    summary.errors.connect, summary.errors.read, summary.errors.write, summary.errors.status, summary.errors.timeout))
end
