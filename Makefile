.DEFAULT_GOAL := help
.PHONY: help install run graph

# `make install && make run` from a fresh clone (rules.md). Needs elan (it installs the Lean
# toolchain named in lean-toolchain), git, curl and python3. If `lake` is not on PATH but elan is
# installed in the usual place, use it from there.
ELAN_BIN := $(or $(ELAN_HOME),$(HOME)/.elan)/bin
ifeq ($(shell command -v lake 2>/dev/null),)
  ifneq ($(wildcard $(ELAN_BIN)/lake),)
    export PATH := $(ELAN_BIN):$(PATH)
  endif
endif

define need_lake
command -v lake >/dev/null 2>&1 || { \
  echo "error: lake (Lean's build tool) not found. Install elan, which provides it:"; \
  echo "  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"; \
  echo "then open a new shell (or run: . ~/.elan/env) and try again."; exit 1; }
endef

define need_python
command -v python3 >/dev/null 2>&1 || { echo "error: python3 not found (needed to drive zrdtd)"; exit 1; }
endef

ZRDTD := core/.lake/build/bin/zrdtd

help: ## Show this help (targets are documented by the "##" comment on their line)
	@grep -E '^[a-zA-Z0-9_-]+:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "}; {printf "  \033[1m%-16s\033[0m %s\n", $$1, $$2}'

install: ## Build it all: fetch the Mathlib cache, lake build (proofs + axiom gate), build zrdtd
	@$(need_lake)
	@command -v git >/dev/null 2>&1 && command -v curl >/dev/null 2>&1 \
	  || { echo "error: git and curl are needed to fetch Mathlib and its build cache"; exit 1; }
	lake exe cache get
	lake build
	cd core && lake build zrdtd
	@echo "install: done. Next: make run"

run: ## Check it: axiom gate, the 133 test vectors and a 1000-record round trip against zrdtd
	@$(need_lake)
	@$(need_python)
	@echo "[1/3] axiom gate: the 11 advertised theorems use only propext, Classical.choice, Quot.sound"
	@lake -q --log-level=error exe axiom_check
	@cd core && lake -q --log-level=error build zrdtd
	@echo "[2/3] test vectors: zrdtd, compiled from the verified Lean code, gives every expected reply"
	@python3 vectors/zrdtd_client.py vectors $(ZRDTD) vectors/vectors.json
	@echo "[3/3] smoke: 1000 chained records through zrdtd, then saved and opened again"
	@python3 vectors/zrdtd_client.py smoke $(ZRDTD) 1000
	@echo ""
	@echo "All checks passed: the proofs build and use only the three standard axioms, and zrdtd"
	@echo "(the shipped binary) answers every test vector and round-trips a 1000-record chat."
	@echo "The GUI demo (Signal Desktop with zrdt) is in l-adic/signal-desktop-zrdt, branch zrdt:"
	@echo "  make install && make run   there."

graph: ## Import graph of this project's own modules (no Mathlib) -> docs/imports.dot [+ .svg]
	mkdir -p docs
	lake exe graph --to Crdt docs/imports.dot
	@command -v dot >/dev/null 2>&1 && dot -Tsvg docs/imports.dot -o docs/imports.svg && echo "wrote docs/imports.svg" || echo "graphviz not installed; wrote docs/imports.dot only"

# zrdtd, its vectors and its closure check (docs/PLAN.md §4 C, §6 rungs 2a and 6). These run
# inside core/ (package zrdt-core: Init and Std only) and never build Mathlib.
.PHONY: zrdtd vectors closure

zrdtd: ## Build the zrdtd daemon (core/, no Mathlib) -> core/.lake/build/bin/zrdtd
	cd core && lake build zrdtd

vectors: ## Regenerate vectors/vectors.json from core/Zrdt/Vectors.lean (printed by core/Zrdtd/Vectors.lean)
	mkdir -p vectors
	cd core && lake build && lake env lean --run Zrdtd/Vectors.lean > ../vectors/vectors.json.tmp
	mv vectors/vectors.json.tmp vectors/vectors.json

closure: ## Check the linked zrdtd: only Init, Std, zrdt-core (and runtime libuv) initializers, no lean_initialize; silent if OK
	@cd core && lake -q --log-level=error build zrdtd
	@bad=$$(nm $(ZRDTD) | awk '{print $$NF}' | sed 's/^_//' \
	  | grep -E '^((runtime_|meta_)?initialize_[A-Za-z]|lean_initialize$$)|[Mm]athlib' \
	  | grep -vE '^(runtime_|meta_)?initialize_(Init|Std|zrdt_x2dcore)(_|$$)|^initialize_libuv$$' \
	  | sort -u); \
	if [ -n "$$bad" ]; then \
	  echo "closure check failed: $(ZRDTD) links $$(echo "$$bad" | wc -l) other initializers, e.g.:"; \
	  echo "$$bad" | head -10; exit 1; fi

# Comparator (docs/PLAN.md §5, claude.md §3 and §7): the advertised statements of
# Crdt/Merkle/Api.lean and Zrdt.encode_injective, restated with `sorry` in
# Comparator/Challenge.lean, judged against the solution module Crdt.Merkle.Api, per comparator.json.
#
# Two ways to run the official comparator (github.com/leanprover/comparator):
#  - built into Lake from Lean v4.35.0 (this toolchain): `lake comparator --config comparator.json`,
#    which needs a `bwrap` that can create user namespaces (Linux; on Ubuntu 23.10+ AppArmor blocks
#    that unless bwrap has a profile). This is the default.
#  - the standalone tool: `lake env <comparator> comparator.json`, with `lean4export` and `landrun`
#    on PATH. `make comparator-tools` clones and builds all three into .tools/; once
#    .tools/comparator is built (or COMPARATOR=/path/to/comparator is given), `make comparator`
#    uses it, with .tools/bin first on PATH.
#
# Both re-check all of Mathlib and have needed over 60 GB, so they run under a memory cap:
# systemd-run --user --scope with MemoryMax=$(MEMORY_MAX) and no swap where available
# (MEMORY_MAX=... to change it), otherwise plain with a warning. `install` and `run` never run them.
.PHONY: comparator-tools comparator check comparator-local

MEMORY_MAX ?= 48G
TOOLS := $(CURDIR)/.tools
BWRAP := $(or $(COMPARATOR_BWRAP),bwrap)
COMPARATOR ?= $(wildcard $(TOOLS)/comparator/.lake/build/bin/comparator)

# $(call capped,command): run command under the memory cap if systemd-run --user works.
define capped
if command -v systemd-run >/dev/null 2>&1 \
   && systemd-run --user --scope -q -p MemoryMax=64M -- true >/dev/null 2>&1; then \
  echo "memory cap: MemoryMax=$(MEMORY_MAX), MemorySwapMax=0 (systemd-run --user --scope)"; \
  systemd-run --user --scope -q -p MemoryMax=$(MEMORY_MAX) -p MemorySwapMax=0 -- $(1); \
else \
  echo "warning: systemd-run --user is not available; running without a memory cap (this has needed over 60 GB)"; \
  $(1); \
fi
endef

define need_bwrap
command -v $(BWRAP) >/dev/null 2>&1 || { \
  echo "error: bubblewrap ($(BWRAP)) not found; lake comparator / lake check run the project inside it."; \
  echo "  Debian/Ubuntu: sudo apt install bubblewrap   Fedora: sudo dnf install bubblewrap"; \
  echo "  or set COMPARATOR_BWRAP, or use the standalone tool: make comparator-tools"; exit 1; }; \
$(BWRAP) --ro-bind / / --unshare-all --die-with-parent true >/dev/null 2>&1 || { \
  echo "error: $(BWRAP) cannot create user namespaces here (on Ubuntu, AppArmor restricts them)."; \
  echo "  Give bwrap an AppArmor profile with 'userns,' (needs root), or use: make comparator-tools"; exit 1; }
endef

# Every module of ours: the spec and proofs (Crdt) and the shipped code (core/Zrdt).
OWN_MODULES = $(shell find Crdt core/Zrdt -name '*.lean' | sed -e 's|^core/||' -e 's|\.lean$$||' -e 's|/|.|g' | sort)

comparator-tools: ## Clone and build the standalone comparator, lean4export and landrun into .tools/ (needs go for landrun)
	@$(need_lake)
	@command -v go >/dev/null 2>&1 || { echo "error: go is needed to build landrun (https://go.dev/dl/)"; exit 1; }
	mkdir -p $(TOOLS)/bin
	test -d $(TOOLS)/comparator || git clone --depth 1 https://github.com/leanprover/comparator $(TOOLS)/comparator
	test -d $(TOOLS)/lean4export || git clone --depth 1 https://github.com/leanprover/lean4export $(TOOLS)/lean4export
	test -d $(TOOLS)/landrun || git clone --depth 1 https://github.com/Zouuup/landrun $(TOOLS)/landrun
	cd $(TOOLS)/comparator && lake build
	cd $(TOOLS)/lean4export && lake build
	cd $(TOOLS)/landrun && go build -o $(TOOLS)/bin/landrun ./cmd/landrun
	ln -sf $(TOOLS)/lean4export/.lake/build/bin/lean4export $(TOOLS)/bin/lean4export
	@echo "comparator-tools: done ($(TOOLS)). make comparator now uses the standalone comparator."

comparator: ## MEMORY-HEAVY (re-checks Mathlib; capped, MEMORY_MAX=48G): judge Api.lean vs Comparator/Challenge.lean
	@$(need_lake)
	lake build Comparator.Challenge
ifneq ($(strip $(COMPARATOR)),)
	@PATH="$(TOOLS)/bin:$$PATH"; export PATH; \
	  for t in lean4export landrun; do command -v $$t >/dev/null 2>&1 \
	    || { echo "error: $$t not on PATH or in $(TOOLS)/bin (make comparator-tools builds it)"; exit 1; }; done; \
	  echo "standalone comparator: $(COMPARATOR)"; \
	  $(call capped,lake env $(COMPARATOR) comparator.json)
else
	@$(need_bwrap)
	@echo "built-in comparator: lake comparator --config comparator.json"
	@$(call capped,lake comparator --config comparator.json)
endif

check: ## MEMORY-HEAVY (re-checks Mathlib; capped, MEMORY_MAX=48G): replay the default targets with `lake check`
	@$(need_lake)
	@$(need_bwrap)
	@$(call capped,lake check)

comparator-local: ## MEMORY-HEAVY (capped), no sandbox, NOT the verdict: statements + axioms, then leanchecker
	lake build Comparator.Challenge $(OWN_MODULES)
	@$(call capped,lake env lean --run scripts/CompareStatements.lean)
	@$(call capped,lake env leanchecker $(OWN_MODULES))
