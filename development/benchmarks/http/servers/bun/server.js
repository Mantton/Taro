function records() {
  const rows = [];
  for (let id = 0; id < 20; id++) rows.push({ id, message: `record ${id}` });
  return rows;
}
const recordsJSON = JSON.stringify(records());
function staticRecords() {
  return new Response(recordsJSON, { headers: { "Content-Type": "application/json" } });
}

Bun.serve({
  hostname: "127.0.0.1",
  port: Number(Bun.argv[2]),
  idleTimeout: 30,
  fetch(request) {
    switch (new URL(request.url).pathname) {
      case "/text":
        return new Response("Hello, World!", {
          headers: { "Content-Type": "text/plain; charset=utf-8" },
        });
      case "/json":
        return Response.json({ message: "Hello, World!" });
      case "/json-static":
        return new Response('{"message":"Hello, World!"}', {
          headers: { "Content-Type": "application/json" },
        });
      case "/stage/static":
        return staticRecords();
      case "/stage/sleep":
        return Bun.sleep(1).then(() => staticRecords());
      case "/stage/encode":
        return Response.json(records());
      case "/app":
        return Bun.sleep(1).then(() => Response.json(records()));
      default:
        return new Response("Not Found", { status: 404 });
    }
  },
});
