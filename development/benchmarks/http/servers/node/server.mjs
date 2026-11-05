import http from "node:http";

function records() {
  const rows = [];
  for (let id = 0; id < 20; id++) rows.push({ id, message: `record ${id}` });
  return rows;
}
const recordsJSON = JSON.stringify(records());
function sendJSON(response, body) {
  response.setHeader("Content-Type", "application/json");
  response.end(body);
}

const server = http.createServer({ keepAliveTimeout: 30_000 }, (request, response) => {
  switch (request.url) {
    case "/text":
      response.setHeader("Content-Type", "text/plain; charset=utf-8");
      response.end("Hello, World!");
      break;
    case "/json":
      response.setHeader("Content-Type", "application/json");
      response.end(JSON.stringify({ message: "Hello, World!" }));
      break;
    case "/stage/static":
      sendJSON(response, recordsJSON);
      break;
    case "/stage/sleep":
      setTimeout(() => sendJSON(response, recordsJSON), 1);
      break;
    case "/stage/encode":
      sendJSON(response, JSON.stringify(records()));
      break;
    // A handler's usual shape: wait as if for a query, then serialize its rows.
    case "/app":
      setTimeout(() => sendJSON(response, JSON.stringify(records())), 1);
      break;
    case "/json-static":
      response.setHeader("Content-Type", "application/json");
      response.end('{"message":"Hello, World!"}');
      break;
    default:
      response.writeHead(404);
      response.end("Not Found");
  }
});
server.listen(Number(process.argv[2]), process.env.BENCH_HOST ?? "127.0.0.1");
