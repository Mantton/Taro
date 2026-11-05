// Foundation DOM and synthesized Codable, with fresh results each iteration.
import Foundation
import CoreFoundation

struct Geometry: Decodable { let type: String; let coordinates: [[[Double]]] }
struct Properties: Decodable { let name: String }
struct Feature: Decodable { let type: String; let properties: Properties; let geometry: Geometry }
struct Canada: Decodable { let type: String; let features: [Feature] }
struct Shape {
    var objects: UInt64 = 0, arrays: UInt64 = 0, strings: UInt64 = 0, numbers: UInt64 = 0
    var booleans: UInt64 = 0, nulls: UInt64 = 0, utf8_bytes: UInt64 = 0, depth: UInt64 = 0
}
func inspect(_ value: Any, _ shape: inout Shape, _ depth: UInt64) {
    shape.depth = max(shape.depth, depth)
    if value is NSNull { shape.nulls += 1 }
    else if let number = value as? NSNumber {
        if CFGetTypeID(number) == CFBooleanGetTypeID() { shape.booleans += 1 }
        else { shape.numbers += 1 }
    } else if let text = value as? String { shape.strings += 1; shape.utf8_bytes += UInt64(text.utf8.count) }
    else if let array = value as? NSArray {
        shape.arrays += 1
        for child in array { inspect(child, &shape, depth + 1) }
    } else if let object = value as? NSDictionary {
        shape.objects += 1
        for (key, child) in object {
            shape.utf8_bytes += UInt64((key as! String).utf8.count)
            inspect(child, &shape, depth + 1)
        }
    } else { fatalError("unknown JSON value") }
}
func top(_ value: Any) -> UInt64 {
    if let object = value as? NSDictionary { return UInt64(object.count) }
    if let array = value as? NSArray { return UInt64(array.count) }
    if let text = value as? String { return UInt64(text.utf8.count) }
    return 1
}
func operation(_ input: Data, _ mode: String, _ decoder: JSONDecoder) -> UInt64 {
    autoreleasepool {
        if mode == "dom" {
            let value = try! JSONSerialization.jsonObject(with: input, options: [.fragmentsAllowed])
            return withExtendedLifetime(value) { top(value) }
        }
        let value = try! decoder.decode(Canada.self, from: input)
        return withExtendedLifetime(value) { UInt64(value.features.count) }
    }
}
func check(_ input: Data, _ mode: String, _ decoder: JSONDecoder) throws {
    if mode == "dom" {
        let value = try JSONSerialization.jsonObject(with: input, options: [.fragmentsAllowed])
        var s = Shape(); inspect(value, &s, 0)
        print("shape objects=\(s.objects) arrays=\(s.arrays) strings=\(s.strings) numbers=\(s.numbers) booleans=\(s.booleans) nulls=\(s.nulls) utf8_bytes=\(s.utf8_bytes) depth=\(s.depth) top=\(top(value))")
        return
    }
    let value = try decoder.decode(Canada.self, from: input)
    precondition(value.type == "FeatureCollection")
    var rings = 0, points = 0, coordinates = 0, sum = 0.0
    for feature in value.features {
        precondition(feature.type == "Feature" && feature.properties.name == "Canada" && feature.geometry.type == "Polygon")
        for ring in feature.geometry.coordinates {
            rings += 1
            for point in ring {
                precondition(point.count == 2); points += 1
                for coordinate in point { coordinates += 1; sum += coordinate }
            }
        }
    }
    print("typed features=\(value.features.count) rings=\(rings) points=\(points) coordinates=\(coordinates) float_sum=\(sum)")
}
func run() throws {
    precondition(CommandLine.arguments.count == 6, "usage: corpus <check|run|audit> <dom|typed> <file> <count> <samples>")
    let args = CommandLine.arguments, action = args[1], mode = args[2]
    precondition(mode == "dom" || mode == "typed")
    let input = try autoreleasepool { try Data(contentsOf: URL(fileURLWithPath: args[3])) }
    precondition(input.count <= 100 * 1024 * 1024)
    let decoder = JSONDecoder()
    if action == "check" { try check(input, mode, decoder); return }
    let count = Int(args[4])!, samples = Int(args[5])!
    precondition(count > 0 && samples > 0 && samples <= 20)
    _ = operation(input, mode, decoder)
    var times = [UInt64](repeating: 0, count: samples), sums = times
    for sample in 0..<samples {
        var checksum: UInt64 = 0
        let start = DispatchTime.now().uptimeNanoseconds
        for _ in 0..<count { checksum += operation(input, mode, decoder) }
        times[sample] = DispatchTime.now().uptimeNanoseconds - start
        sums[sample] = checksum
    }
    if action == "run" {
        for sample in 0..<samples { print("sample ns=\(times[sample]) ops=\(count) checksum=\(sums[sample])") }
    }
    print("stats ops=\(count * samples) gc_model=arc")
}
try run()
