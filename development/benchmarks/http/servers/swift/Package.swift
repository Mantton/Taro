// swift-tools-version: 6.0
import PackageDescription
let package = Package(
    name: "HTTPComparison",
    platforms: [.macOS(.v14)],
    dependencies: [
        .package(url: "https://github.com/hummingbird-project/hummingbird.git", exact: "2.28.1"),
        .package(url: "https://github.com/apple/swift-nio.git", exact: "2.105.0"),
    ],
    targets: [.executableTarget(name: "Server", dependencies: [
        .product(name: "Hummingbird", package: "hummingbird"),
        .product(name: "NIOPosix", package: "swift-nio"),
    ])]
)
