SHELL := /bin/sh

PYTHON ?= python3
CARGO ?= cargo
ROOT := $(CURDIR)

BUILD_DIST := $(ROOT)/development/scripts/build_dist.py
RUN_DIST := $(ROOT)/development/scripts/run_dist.py
LANGUAGE_TESTS := $(ROOT)/development/scripts/language_tests.py
TEST_ALL := $(ROOT)/development/scripts/test_all.py
BENCHMARK_TIMINGS := $(ROOT)/development/scripts/benchmark_timings.py
CODEGEN_BENCHMARK := $(ROOT)/development/scripts/codegen_benchmarks.py
RUNTIME_STRESS := $(ROOT)/development/scripts/runtime_stress.py
LLVM_TOOLCHAIN := $(ROOT)/development/scripts/llvm_toolchain.py
LLVM_TOOLCHAIN_TESTS := $(ROOT)/development/scripts/test_llvm_toolchain.py
CODEGEN_MATRIX := $(ROOT)/language_tests/codegen_matrix.txt

DIST_DIR := $(ROOT)/dist
TARO := $(DIST_DIR)/bin/taro
STD_PATH := $(ROOT)/std

.PHONY: help llvm-check llvm-tests compiler compiler-release lsp lsp-release lsp-bin lsp-release-bin dist run check cargo-test test language-tests codegen-matrix std-tests runtime-stress all-tests bench benchmark codegen-benchmark

help:
	@echo "Taro development shortcuts"
	@echo ""
	@echo "Build:"
	@echo "  make llvm-check               Show the LLVM 22.1 toolchain used by Taro"
	@echo "  make compiler                 Build taro-bin (debug)"
	@echo "  make compiler-release         Build taro-bin (release)"
	@echo "  make lsp                      Build dist/ and taro-lsp (debug)"
	@echo "  make lsp-release              Build dist/ and taro-lsp (release)"
	@echo "  make lsp-bin                  Build taro-lsp only (debug)"
	@echo "  make lsp-release-bin          Build taro-lsp only (release)"
	@echo "  make dist                     Build dist/ layout (compiler + runtime + std link)"
	@echo ""
	@echo "Run compiler:"
	@echo "  make run FILE=examples/hello.tr"
	@echo "  make check FILE=examples/hello.tr"
	@echo ""
	@echo "Tests:"
	@echo "  make llvm-tests               Run LLVM toolchain resolver tests"
	@echo "  make test                     Run cargo workspace tests"
	@echo "  make language-tests           Run language tests"
	@echo "  make language-tests JOBS=4"
	@echo "  make language-tests FILTER=optional"
	@echo "  make codegen-matrix           Run high-risk codegen tests with strict GlobalISel fallback checks"
	@echo "  make codegen-matrix JOBS=4"
	@echo "  make codegen-matrix OPT_LEVEL=2"
	@echo "  make std-tests                Run std package test files"
	@echo "  make runtime-stress           Run runtime-tagged std stress tests across worker counts"
	@echo "  make all-tests                Run full test_all.py pipeline"
	@echo "  make all-tests JOBS=4"
	@echo ""
	@echo "Benchmarks:"
	@echo "  make bench PACKAGE=path       Run Taro @bench functions"
	@echo "  make bench PACKAGE=path BENCH_ARGS='--filter parse --time 2s'"
	@echo "  make benchmark PACKAGE=std"
	@echo "  make benchmark PACKAGE=std RUNS=10"
	@echo "  make codegen-benchmark        Compare release baseline and O2 code generation"
	@echo "  make codegen-benchmark RUNS=10"

llvm-check:
	$(PYTHON) $(LLVM_TOOLCHAIN)

llvm-tests:
	$(PYTHON) $(LLVM_TOOLCHAIN_TESTS)

compiler:
	$(PYTHON) $(LLVM_TOOLCHAIN) $(CARGO) build -p taro-bin

compiler-release:
	$(PYTHON) $(LLVM_TOOLCHAIN) $(CARGO) build -p taro-bin --release

lsp:
	$(PYTHON) $(BUILD_DIST) --profile debug

lsp-release:
	$(PYTHON) $(BUILD_DIST) --profile release

lsp-bin:
	$(PYTHON) $(LLVM_TOOLCHAIN) $(CARGO) build -p taro-lsp

lsp-release-bin:
	$(PYTHON) $(LLVM_TOOLCHAIN) $(CARGO) build -p taro-lsp --release

dist:
	$(PYTHON) $(BUILD_DIST)

run:
	@if [ -z "$(FILE)" ]; then \
		echo "error: FILE is required (example: make run FILE=examples/hello.tr)"; \
		exit 1; \
	fi
	$(PYTHON) $(RUN_DIST) $(FILE)

check: dist
	@if [ -z "$(FILE)" ]; then \
		echo "error: FILE is required (example: make check FILE=examples/hello.tr)"; \
		exit 1; \
	fi
	TARO_HOME=$(DIST_DIR) $(TARO) check $(FILE) --std-path $(STD_PATH)

cargo-test:
	$(PYTHON) $(LLVM_TOOLCHAIN) $(CARGO) test --workspace

test: cargo-test

language-tests:
	$(PYTHON) $(LANGUAGE_TESTS) $(if $(FILTER),--filter $(FILTER),) $(if $(JOBS),--jobs $(JOBS),)

codegen-matrix:
	TARO_LLVM_STRICT_GLOBAL_ISEL=1 $(PYTHON) $(LANGUAGE_TESTS) --manifest $(CODEGEN_MATRIX) --codegen-profile both $(if $(OPT_LEVEL),--opt-level $(OPT_LEVEL),) $(if $(JOBS),--jobs $(JOBS),)

std-tests: dist
	$(PYTHON) $(TEST_ALL) --skip-cargo-tests --skip-build-dist --skip-language-tests

runtime-stress:
	$(PYTHON) $(RUNTIME_STRESS)

all-tests:
	$(PYTHON) $(TEST_ALL) $(if $(JOBS),--jobs $(JOBS),)

bench: dist
	@if [ -z "$(PACKAGE)" ]; then \
		echo "error: PACKAGE is required (example: make bench PACKAGE=path/to/package)"; \
		exit 1; \
	fi
	TARO_HOME=$(DIST_DIR) $(TARO) bench $(PACKAGE) --std-path $(STD_PATH) $(BENCH_ARGS)

benchmark:
	@if [ -z "$(PACKAGE)" ]; then \
		echo "error: PACKAGE is required (example: make benchmark PACKAGE=std)"; \
		exit 1; \
	fi
	$(PYTHON) $(BENCHMARK_TIMINGS) $(PACKAGE) $(if $(RUNS),--runs $(RUNS),)

codegen-benchmark:
	$(PYTHON) $(CODEGEN_BENCHMARK) $(if $(FILE),$(FILE),) $(if $(RUNS),--runs $(RUNS),)
