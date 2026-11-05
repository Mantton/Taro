// Foundation reference for the typed record cases in ../src/records.tr.
import Foundation

struct Person: Codable, Equatable {
    let name: String
    let age: UInt8
}

final class ResultSink {
    var person = Person(name: "", age: 0)
    var people: [Person] = []
    var data = Data()
}

func requireEqual<T: Equatable>(_ actual: T, _ expected: T) {
    precondition(actual == expected, "record round trip mismatch")
}

func batch(_ count: Int, _ operation: () -> Void) -> UInt64 {
    let start = DispatchTime.now().uptimeNanoseconds
    // Include draining temporary Objective-C objects in each batch's time.
    autoreleasepool {
        for _ in 0..<count { operation() }
    }
    return DispatchTime.now().uptimeNanoseconds - start
}

func run(_ which: String) throws {
    let one = #"{"name":"Ada","age":37}"#
    let array = "[" + Array(repeating: one, count: 128).joined(separator: ",") + "]"
    let input = Data((which.hasSuffix("People128") ? array : one).utf8)
    // Reuse configuration objects, but decode fresh values and encode fresh
    // output every iteration. Default key order is not a wire-format contract.
    let encoder = JSONEncoder()
    let decoder = JSONDecoder()
    let sink = ResultSink()
    let operation: () -> Void
    let person: Person
    let people: [Person]
    if which == "encodePerson" || which == "decodePerson" {
        person = try decoder.decode(Person.self, from: input)
        people = []
        requireEqual(person, Person(name: "Ada", age: 37))
        let encoded = try encoder.encode(person)
        precondition(encoded.count == input.count)
        requireEqual(try decoder.decode(Person.self, from: encoded), person)
    } else {
        person = Person(name: "", age: 0)
        people = try decoder.decode([Person].self, from: input)
        requireEqual(people, Array(repeating: Person(name: "Ada", age: 37), count: 128))
        let encoded = try encoder.encode(people)
        precondition(encoded.count == input.count)
        requireEqual(try decoder.decode([Person].self, from: encoded), people)
    }
    switch which {
    case "encodePerson": operation = { sink.data = try! encoder.encode(person) }
    case "encodePeople128": operation = { sink.data = try! encoder.encode(people) }
    case "decodePerson": operation = { sink.person = try! decoder.decode(Person.self, from: input) }
    case "decodePeople128": operation = { sink.people = try! decoder.decode([Person].self, from: input) }
    default: fatalError("expected encodePerson, decodePerson, encodePeople128 or decodePeople128")
    }
    var count = 1
    var elapsed: UInt64
    repeat {
        elapsed = batch(count, operation)
        if elapsed < 100_000_000 { count *= 2 }
    } while elapsed < 100_000_000
    count = max(1, Int(Double(count) * 50_000_000 / Double(elapsed)))
    var samples: [Double] = []
    samples.reserveCapacity(20)
    for _ in 0..<20 { samples.append(Double(batch(count, operation)) / Double(count)) }
    switch which {
    case "encodePerson": requireEqual(try decoder.decode(Person.self, from: sink.data), person)
    case "encodePeople128": requireEqual(try decoder.decode([Person].self, from: sink.data), people)
    case "decodePerson": precondition(sink.person == person)
    default: precondition(sink.people == people)
    }
    let report: [String: Any] = [
        "case": which, "samples_ns_per_op": samples,
        "iterations_per_sample": count, "bytes_per_iteration": input.count,
    ]
    let output = try JSONSerialization.data(withJSONObject: report, options: [.sortedKeys])
    print(String(decoding: output, as: UTF8.self))
}

guard CommandLine.arguments.count == 2 else { fatalError("expected case") }
try run(CommandLine.arguments[1])
