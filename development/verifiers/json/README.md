# JSON verifier

This project certifies Taro's public `std.json` parser and streaming decoder against ten
independently maintained JSON corpora. The selected inputs are pinned by immutable upstream
revision, license digest, file count, byte count, and a byte-stable tree SHA-256. None of the
third-party inputs are stored in this repository.

| Suite | Inputs | What it contributes |
| --- | ---: | --- |
| [JSONTestSuite](https://github.com/nst/JSONTestSuite) | 318 | Broad RFC acceptance, rejection, and interoperability cases |
| [Jansson](https://github.com/akheron/jansson) | 103 | Valid, invalid, malformed-Unicode, and numeric-boundary cases |
| [YAJL](https://github.com/lloyd/yajl) | 58 | Strict parsing and extension-boundary cases |
| [yyjson](https://github.com/ibireme/yyjson) | 209 | Modern strict-parser, Unicode, number, and extension cases |
| [JsonCpp](https://github.com/open-source-parsers/jsoncpp) | 69 | Parser regressions and extension rejection cases |
| [JSON Schema Test Suite](https://github.com/json-schema-org/JSON-Schema-Test-Suite) | 513 | Larger real-world schema and remote documents |
| [JSON Canonicalization Scheme](https://github.com/cyberphone/json-canonicalization) | 12 | Numeric, Unicode, and object-shaped documents |
| [Big List of Naughty Strings](https://github.com/minimaxir/big-list-of-naughty-strings) | 1 | A string-heavy adversarial document |
| [Boost.JSON](https://github.com/boostorg/json) | 16 | Parser-crash regression inputs |
| [cJSON](https://github.com/DaveGamble/cJSON) | 14 | Fuzzer seed inputs |

The committed manifests under `corpora/` document the exact selection and licensing policy. We
exclude mirrors of the same conformance corpus because duplicate cases add runtime without adding
independent evidence, and exclude sources without an explicit redistribution/use license.

## Prepare inputs

Prepare every pinned suite once:

```sh
make verify-json-prepare
```

Preparation is the only operation that uses the network. It validates each source before
atomically publishing normalized inputs under
`target/verifiers/json/<suite>/<revision>/`, which is ignored by Git. `fetch = "files"` downloads
only selected source files; `fetch = "archive"` validates a bounded in-memory archive and retains
only selected files. Use `REFRESH=1` to replace a damaged or intentionally stale cache:

```sh
make verify-json-prepare REFRESH=1
```

For a focused download, invoke the runner directly with one or more suite IDs:

```sh
python3 development/verifiers/json/verify.py prepare --suite yyjson
```

## Run certification

Run all prepared suites without network access:

```sh
make verify-json
```

The full certification covers 1,313 inputs and 12,600 parser runs. Conformance and fuzz suites use
the `full` matrix: an RFC-oriented profile and the safety-oriented public defaults, each in
one-shot mode and streaming mode with chunk sizes 1, 2, 3, 7, and 4096 bytes. Large collections of
known-valid documents use the `documents` matrix: both profiles in one-shot mode and streaming
mode with chunk sizes 7 and 4096 bytes. The smaller matrix preserves boundary and buffering
coverage without multiplying the slowest, least adversarial inputs.

Required documents must be accepted by the RFC profile, and forbidden documents must be rejected
by both profiles. The safe profile may reject otherwise valid inputs only because of its documented
duplicate-key, depth, or input-size limits. Implementation-defined inputs record the parser's
choice while still requiring deterministic one-shot/streaming behavior. Every accepted value must
survive stringify/parse/stringify canonically, and every error must expose valid byte, line,
column, and JSON-path diagnostics.

Run one suite or request all implementation decisions with:

```sh
python3 development/verifiers/json/verify.py run --suite json-test-suite
python3 development/verifiers/json/verify.py run --verbose
```

No machine-specific report is committed. Runner regressions use generated fixtures and remain
offline:

```sh
python3 -m unittest discover -s development/verifiers/json -p 'test_*.py'
```
