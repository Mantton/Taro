-- wrk script for stress.py. STRESS_DEPTH sets the HTTP pipeline depth.
local depth = tonumber(os.getenv("STRESS_DEPTH") or "1")
local pipeline

function init(args)
  local requests = {}
  for index = 1, depth do
    requests[index] = wrk.format()
  end
  pipeline = table.concat(requests)
end

function request()
  return pipeline
end

function done(summary, latency, requests)
  io.write(string.format(
    "{\"requests\":%d,\"duration_us\":%d,\"bytes\":%d,\"p50_us\":%d,\"p99_us\":%d,\"max_us\":%d,"
      .. "\"connect_errors\":%d,\"read_errors\":%d,\"write_errors\":%d,\"status_errors\":%d,\"timeouts\":%d}\n",
    summary.requests, summary.duration, summary.bytes,
    latency:percentile(50), latency:percentile(99), latency.max,
    summary.errors.connect, summary.errors.read, summary.errors.write,
    summary.errors.status, summary.errors.timeout))
end
