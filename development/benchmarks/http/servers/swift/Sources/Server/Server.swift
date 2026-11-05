import Foundation
import Hummingbird
import NIOPosix

struct Message: ResponseEncodable { let message: String }
struct Record: ResponseEncodable {
    let id: Int
    let message: String
}

func records() -> [Record] {
    (0..<20).map { Record(id: $0, message: "record \($0)") }
}

func staticRecords(_ json: String) -> Response {
    Response(status: .ok, headers: [.contentType: "application/json"],
        body: .init(byteBuffer: .init(string: json)))
}

@main
struct Main {
    static func main() async throws {
        let port = Int(CommandLine.arguments[1])!
        let workers = Int(ProcessInfo.processInfo.environment["BENCH_WORKERS"]!)!
        let group = MultiThreadedEventLoopGroup(numberOfThreads: workers)
        let recordsJSON = String(decoding: try JSONEncoder().encode(records()), as: UTF8.self)
        let router = Router()
        router.get("/text") { _, _ -> String in "Hello, World!" }
        router.get("/json") { _, _ -> Message in Message(message: "Hello, World!") }
        router.get("/json-static") { _, _ -> Response in
            Response(status: .ok, headers: [.contentType: "application/json"], body: .init(byteBuffer: .init(string: #"{"message":"Hello, World!"}"#)))
        }
        router.get("/stage/static") { _, _ -> Response in staticRecords(recordsJSON) }
        router.get("/stage/sleep") { _, _ -> Response in
            try await Task.sleep(for: .milliseconds(1))
            return staticRecords(recordsJSON)
        }
        router.get("/stage/encode") { _, _ -> [Record] in records() }
        router.get("/app") { _, _ -> [Record] in
            try await Task.sleep(for: .milliseconds(1))
            return records()
        }
        let app = Application(router: router,
            configuration: .init(address: .hostname("127.0.0.1", port: port)),
            eventLoopGroupProvider: .shared(group))
        try await app.runService()
        try await group.shutdownGracefully()
    }
}
