SHELL := /bin/sh

PYTHON ?= python3
SHOWCASE_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
ROOT := $(abspath $(SHOWCASE_DIR)/../..)
BUILD_DIST := $(ROOT)/development/scripts/build_dist.py
VERIFIER := $(ROOT)/development/verifiers/adex_iris/verify.py

.DEFAULT_GOAL := help
.PHONY: help dist prepare verify

help:
	@echo "AdEx Iris showcase"
	@echo ""
	@echo "  make prepare          Download and validate the pinned UCI Iris data"
	@echo "  make verify           Build Taro and run the offline classifier verification"

dist:
	$(PYTHON) $(BUILD_DIST)

prepare:
	$(PYTHON) $(VERIFIER) prepare $(if $(REFRESH),--refresh,)

verify: dist
	$(PYTHON) $(VERIFIER) run
