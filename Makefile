SHELL := /bin/sh

PYTHON ?= python3
CARGO ?= cargo
ROOT := $(CURDIR)

BUILD_DIST := $(ROOT)/development/scripts/build_dist.py
RUN_DIST := $(ROOT)/development/scripts/run_dist.py
LANGUAGE_TESTS := $(ROOT)/development/scripts/language_tests.py
TEST_ALL := $(ROOT)/development/scripts/test_all.py
BENCHMARK_TIMINGS := $(ROOT)/development/scripts/benchmark_timings.py

DIST_DIR := $(ROOT)/dist
TARO := $(DIST_DIR)/bin/taro
STD_PATH := $(ROOT)/std

.PHONY: help compiler compiler-release dist run check cargo-test test language-tests std-tests all-tests benchmark

help:
	@echo "Taro development shortcuts"
	@echo ""
	@echo "Build:"
	@echo "  make compiler                 Build taro-bin (debug)"
	@echo "  make compiler-release         Build taro-bin (release)"
	@echo "  make dist                     Build dist/ layout (compiler + runtime + std link)"
	@echo ""
	@echo "Run compiler:"
	@echo "  make run FILE=examples/hello.tr"
	@echo "  make check FILE=examples/hello.tr"
	@echo ""
	@echo "Tests:"
	@echo "  make test                     Run cargo workspace tests"
	@echo "  make language-tests           Run language tests"
	@echo "  make language-tests JOBS=4"
	@echo "  make language-tests FILTER=optional"
	@echo "  make std-tests                Run std package test files"
	@echo "  make all-tests                Run full test_all.py pipeline"
	@echo "  make all-tests JOBS=4"
	@echo ""
	@echo "Benchmarks:"
	@echo "  make benchmark PACKAGE=std"
	@echo "  make benchmark PACKAGE=std RUNS=10"
compiler:
	$(CARGO) build -p taro-bin

compiler-release:
	$(CARGO) build -p taro-bin --release

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
	$(CARGO) test --workspace

test: cargo-test

language-tests:
	$(PYTHON) $(LANGUAGE_TESTS) $(if $(FILTER),--filter $(FILTER),) $(if $(JOBS),--jobs $(JOBS),)

std-tests: dist
	$(PYTHON) $(TEST_ALL) --skip-cargo-tests --skip-build-dist --skip-language-tests

all-tests:
	$(PYTHON) $(TEST_ALL) $(if $(JOBS),--jobs $(JOBS),)

benchmark:
	@if [ -z "$(PACKAGE)" ]; then \
		echo "error: PACKAGE is required (example: make benchmark PACKAGE=std)"; \
		exit 1; \
	fi
	$(PYTHON) $(BENCHMARK_TIMINGS) $(PACKAGE) $(if $(RUNS),--runs $(RUNS),)
