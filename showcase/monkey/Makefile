SHELL := /bin/sh

PYTHON ?= python3
SHOWCASE_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
ROOT := $(abspath $(SHOWCASE_DIR)/../..)
BUILD_DIST := $(ROOT)/development/scripts/build_dist.py
HOST_BENCHMARK := $(ROOT)/development/scripts/monkey_host_benchmarks.py
DIST_DIR := $(ROOT)/dist
TARO := $(DIST_DIR)/bin/taro

.DEFAULT_GOAL := help
.PHONY: help dist host-benchmark

help:
	@echo "Monkey showcase"
	@echo ""
	@echo "  make host-benchmark   Compare matched Monkey hot-path workloads with Go"
	@echo "  make host-benchmark QUICK=1"

dist:
	$(PYTHON) $(BUILD_DIST)

host-benchmark: dist
	$(PYTHON) $(HOST_BENCHMARK) --compiler $(TARO) --taro-home $(DIST_DIR) \
		$(if $(RUNS),--runs $(RUNS),) $(if $(WARMUPS),--warmups $(WARMUPS),) \
		$(if $(QUICK),--quick,) $(HOST_BENCH_ARGS)
