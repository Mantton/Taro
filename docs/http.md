# HTTP contract

The standard library owns HTTP transport and exposes small contracts for
external routers, middleware and clients. Handlers receive `&Request` and return
`Result[Response, Error]` asynchronously. Response is a value; its Body is a
shared consumable stream. A reference does not make Request immutable in Taro.
JSON remains single-pass by default with explicit validation-first options.

## Reference review

| Reference | Useful boundary adopted by Taro |
| --- | --- |
| [Go net/http](https://pkg.go.dev/net/http) and [Chi](https://github.com/go-chi/chi) | One common handler contract, reusable clients, explicit request-body cleanup, middleware wrapping ordinary handlers. |
| [Hyper Service](https://docs.rs/hyper/latest/hyper/service/trait.Service.html), [Body](https://docs.rs/hyper/latest/hyper/body/trait.Body.html), [Tower](https://docs.rs/tower/latest/tower/trait.Service.html) and [Axum](https://docs.rs/axum/latest/axum/) | Async request-to-response composition, streamed bodies, transport separate from routing, explicit concurrency/backpressure. |
| [Swift Foundation URLSession](https://developer.apple.com/documentation/foundation/urlsession) | Convenient client calls with async buffered and streaming response APIs. Foundation is a platform library, not Swift's core std library. |
| [Swift AsyncHTTPClient](https://github.com/swift-server/async-http-client/blob/main/Sources/AsyncHTTPClient/AsyncAwait/HTTPClientResponse.swift) and [Hummingbird](https://github.com/hummingbird-project/hummingbird/blob/main/Sources/HummingbirdCore/Response/Response.swift) | Response values containing streaming bodies; bounded body collection is an explicit operation. |

Chi directly composes Go's standard HTTP handlers. [Fiber](https://docs.gofiber.io/)
uses a separate fasthttp engine. Taro's extension point follows the shared-handler
approach: external routing does not require a second HTTP engine. Taro does not
reuse request objects for subsequent exchanges; retained metadata references
continue to describe their original request. GC reachability does not extend a
network body's resource lifetime.

## Handlers and serving

```taro
import std::http::{Request, Response, Server}
import std::net::SocketAddress
import std::result::Result

func hello(_ request: &Request) async -> Result[Response, std::http::Error] {
    return .text(200, request.url)
}

func main() async {
    server := Server::bind(SocketAddress::localhost(8080_u16)).unwrap()
    defer { var _ = server.close() }
    await server.serve(hello).unwrap()
}
```

`Handler.handle(&Request)` is the same async contract for routers and middleware.
`handler(function)` creates an adapter for storage or composition.
`syncHandler(function)` adapts an ordinary function to that contract. Ordinary
handlers run on the executor; use `task.blocking` for blocking operations.
Middleware stores another Handler, calls it, and can edit the returned Response.
No routing or application framework is imposed by the serving loop.

`serve` accepts named async functions directly or a value conforming to Handler.
It admits every connection the process has descriptors for, unless `Options.maxConnections`
sets a limit.
Closing any Server copy stops acceptance; serve drains accepted exchanges before
returning. Cancelling its task cancels and drains exchanges instead. Request and
response bodies close on completion, error, panic and cancellation. Cancellation
is cooperative; application work must reach suspension/cancellation checkpoints.

An unhandled handler Error produces a generic 500 without exposing its message.
A handler deadline produces 504. A handler panic closes its exchange while other
connections remain available. HTTP application errors such as 400 or 404 should
be returned as ordinary Responses. A body failure after headers have been sent
closes the connection; it cannot be replaced with another status.

The lower-level `accept`, `Connection.request` and `Connection.respond` APIs remain
available. Their caller owns cleanup and concurrency. Connections support
sequential HTTP/1.1 exchanges, preserving over-read pipeline bytes. Only completely consumed request bodies permit reuse; unread or
abandoned bodies force connection close. Options.keepAlive disables reuse.
shutdown(Duration) stops acceptance, closes idle sockets and waits for serving
exchanges until its deadline, then closes active sockets and reports timeout.
HEAD suppresses the response body and retains a known representation length; 204/205/304 require a known-empty body and never
poll a producer. Use Body::empty() for those statuses. Private framing
state retains the original method even if a handler changes request metadata.

## Bodies

Body implements `std::io::AsyncReader`. Copies share cursor and close state;
copying a Request or Response does not replay or deep-copy its body. Only one
read can be active. Concurrent reads fail instead of racing a producer.

- `Body::empty()` creates an empty stream.
- `Body::fromString(text)` retains immutable string storage.
- `Body::fromBytes(bytes)` snapshots mutable bytes.
- `Body::fromSource(source, length: optionalLength)` adopts a BodySource producer.
- `readAll(maxBytes: ...)` and `readToString(maxBytes: ...)` collect under a finite
  bound and close on success or error. EOF automatically releases the source.
- `close()` closes shared aliases. During a pending read it acknowledges close;
  producer cleanup waits for that read to finish or be cancelled. Immediate
  close errors are returned; deferred close errors are reported on stderr.

BodySource has async `read(Span[uint8])` and synchronous `close()` methods with
`std::io::Error`. Producers must return at most the supplied span length, return
zero at EOF and stop retaining the span when a read finishes or is cancelled.
Known lengths are checked. Transport and producer errors are terminal. Producer
resources belong to the Body after adoption; external aliases require their own
synchronization and must not independently read/close the producer.

Streaming responses use Content-Length when known, otherwise HTTP/1.1 chunked
framing. Response writing pulls one bounded chunk at a time and awaits socket
writes, providing backpressure. A stream is not collected just to send it.

`request.json[T]()` and `response.json[T]()` are async, consume and close the
body, and return `JsonError.body` or `JsonError.decode` to retain structured
JSON diagnostics. Their JSON Options control collection size and decoding.

## Clients and custom transports

```taro
import std::http::{Body, Client, Request}

func fetch() async {
    client := Client::new().unwrap()
    defer { client.close() }
    request := Request::new("GET", "https://example.com/")
    response := await client.send(&request).unwrap()
    defer { var _ = response.close() }
    text := await response.body.readToString(maxBytes: 1024 * 1024).unwrap()
    std::println(text)
}
```

`Transport.roundTrip(&Request)` performs one exchange. `Client::withTransport(value)`
uses an independently implemented transport, including test transports and
middleware wrappers. This borrows the custom transport: closing Client
invalidates its copies, and the caller owns custom-transport shutdown. The
default client owns and explicitly closes its connection pool.

Client.send takes responsibility for closing the original request Body on every
exit, including validation failures and cancellation. Retrying requires a fresh
Body. Transports must leave request metadata unchanged; wrappers that edit
headers should copy metadata/Headers first. Callers synchronize mutations while
an exchange is active. HTTP error statuses are successful transport responses.

TLS uses [rustls](https://github.com/rustls/rustls) and system certificate/hostname
verification for HTTPS. Redirects are returned unchanged. Client and server
control framing headers to reject ambiguous Content-Length/Transfer-Encoding
and header injection. Native code retains owned bytes, never Taro pointers.

## Limits and implementation stages

Options defaults: 16 KiB headers, 128 headers, 16 MiB body, 30 second operation
and handler deadlines, no configured serving-connection cap, 128 idle client
connections and keep-alive enabled. The default client deadline
covers outbound streaming producers as well as the network exchange. Timeouts are nonzero 32-bit
milliseconds. Header/body limits remain enforced when collecting data. Input
chunk framing has a separate header-sized budget. Explicit close is required
for OS resources; GC is not a socket finalizer.

Implemented foundation: shared streaming Body, Handler/Transport interfaces,
reference-based send, function adapters, middleware composition, configurable
serving limits, streamed/chunked response output and isolated handler failures.
Current Unix backends support macOS/Linux, with focused validation on both.

HTTP/1.1 foundation is implemented: streamed request/response bodies, persistent
connections, bounded serving/shutdown, verified TLS client and server, and
reusable client pooling. HTTP/2, protocol upgrades, CONNECT, Expect/100-continue
uploads and trailers are not implemented. They are separate protocol extensions.

The client returns after final response headers. Its send deadline covers DNS,
connection, TLS, upload and response headers; response body reads have finite
per-read deadlines. Upload completes before response parsing. No automatic retry
or redirect can replay a consumable request body. Framing/producer failures and
early response-body close discard the connection. Completely consumed responses
may return it to a bounded idle pool. Idle expiry is checked lazily on checkout;
Client.close closes pooled sockets. Already active responses remain readable,
but cannot repopulate a closed client. Server keep-alive defaults to true and
Options.keepAlive disables it on either side.

Both client and server socket I/O use the reactor. Only platform DNS uses the
bounded blocking pool and may outlive cancellation; native code never retains a
managed input pointer. TLS record state has bounded native buffers and explicit
close. std::tls::Stream permits one active operation, rejects concurrent I/O,
and closes on cancellation or errors; task.withTimeout supplies caller policy.
TLS supports 1.2/1.3 and negotiates HTTP/1.1 with the maintained provider.

No synchronous networking overloads are introduced in this batch.

## Runnable client and server

[`examples/http_server.tr`](../examples/http_server.tr) serves a small HTML page,
a health endpoint and a typed JSON array of posts. [`examples/http_scraper.tr`](../examples/http_scraper.tr)
fetches that page, extracts its literal title tags, then decodes the posts with
`response.json[List[Post]]()`. `Post: Codable` derives its codecs automatically.
The title helper is intentionally for this simple HTML shape, rather than a
general HTML parser. Both examples use the ordinary public API.

Run these in separate terminals from the repository root:

```sh
taro run examples/http_server.tr
taro run examples/http_scraper.tr
```

The server accepts an optional port. The client accepts a pair of page/JSON URLs;
HTTPS uses the same API and verifies platform trust and hostnames:

```sh
taro run examples/http_server.tr -- 8081
taro run examples/http_scraper.tr -- http://127.0.0.1:8081/ http://127.0.0.1:8081/posts
```

The examples check HTTP status before decoding and bound collection to 1 MiB.
They use `defer` for explicit resource cleanup. Reading to EOF returns eligible
connections to the client's pool, so one Client can serve both fetches. Invalid
application inputs and request failures use `unwrap`/assertions in these small
demos; the API exposes structured `Result` errors for application policy.

Focused tests are in `std/src/tests/http/`. Run at O0/O3, including
`TARO_GC_STRESS=1`. Generated logs and measurements belong in ignored target
storage. Compare server/client separately with one fixed peer, and disable
keep-alive on all peers for connection-per-request baselines.

## HTTPS server and private trust

```taro
config := std::tls::ServerConfig::fromPEM(certificateChainPEM, privateKeyPEM).unwrap()
defer { config.close() }
server := Server::bindTLS(SocketAddress::localhost(8443_u16), config).unwrap()
defer { var _ = server.close() }
await server.serve(hello).unwrap()
```

ServerConfig and explicitly supplied ClientConfig are borrowed by HTTP. Close
configuration after the server/client has finished creating sessions; established
sessions retain their native configuration. The default Client owns its platform
trust configuration. ClientConfig::withRootPEM creates isolated verified roots
for a private service; Client::withTLSConfig uses it without changing system
trust or bypassing hostname verification. Stream close aborts the socket rather
than waiting for a TLS close-notify exchange.
