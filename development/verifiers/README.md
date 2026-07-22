# Taro verifiers

A verifier is a standalone project that exercises Taro against an external contract: a file
format corpus, protocol test suite, ABI fixture, or another independently maintained source of
truth. Verifiers complement focused unit tests; they do not replace them, and they are not
performance benchmarks.

Each verifier lives in `development/verifiers/<contract>` and should contain:

- a standalone Taro package that uses the same public APIs as an application;
- a small runner that validates a versioned result protocol and exits non-zero on disagreement;
- a committed manifest pinning every external input by immutable revision and checksum;
- offline runner tests using generated fixtures; and
- a README documenting preparation, execution, policies, and expected runtime.

External inputs and generated reports belong under `target/verifiers/<contract>`, which is already
ignored. Preparation must be an explicit command, publish its cache only after full validation,
and never be part of the normal test suite. Running a prepared verifier must not require network
access. This split keeps normal development deterministic while still making external evidence
reproducible.

Verifier protocol tests are discovered automatically by `development/scripts/test_all.py`; adding
a project-local `test_*.py` file is sufficient.

Available projects:

- [`json`](json/README.md) checks `std.json` against ten pinned conformance, regression, fuzz, and
  real-document corpora.
