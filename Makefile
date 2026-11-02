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

install: ## Build it all: fetch the Mathlib cache, lake build (proofs + axiom gate), build zrdtd (~9 GB disk)
	@$(need_lake)
	@command -v git >/dev/null 2>&1 && command -v curl >/dev/null 2>&1 \
	  || { echo "error: git and curl are needed to fetch Mathlib and its build cache"; exit 1; }
	lake exe cache get
	lake build
	cd core && lake build zrdtd
	@echo "install: done. Next: make run"

run: ## Check it: axiom gate, the 281 test vectors and a 1000-record round trip against zrdtd
	@$(need_lake)
	@$(need_python)
	@echo "[1/3] axiom gate: the 27 advertised theorems use only propext, Classical.choice, Quot.sound"
	@lake -q --log-level=error lean Test/Axioms.lean && echo "axiom gate passed (Test/Axioms.lean elaborated again; every #guard_msgs matched)"
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
# Two ways to run the official comparator; COMPARATOR=builtin|standalone picks one. Both need
# Linux, and both build the challenge and the solution themselves, inside their sandbox: for a
# verdict you can trust, run `make comparator` in a fresh clone before `make install` (comparator's
# README asks that the solution not be compiled outside the sandbox first).
#  - builtin: `lake comparator --config comparator.json`, built into Lake since Lean v4.35.0 (this
#    toolchain); upstream recommends it. It sandboxes with bubblewrap, which needs unprivileged
#    user namespaces: on Ubuntu 23.10+ AppArmor blocks them unless bwrap has a profile allowing
#    `userns` (README, "Running Comparator", gives the two-line fix; it needs root).
#  - standalone: github.com/leanprover/comparator, archived when it moved into Lake. It sandboxes
#    with landrun (Landlock: no user namespaces, no root). `make comparator-tools` builds it, the
#    lean4export its manifest pins, and landrun, into .tools/. It runs as its README says:
#    `lake env <comparator> comparator.json` in a systemd-run --user service with
#    RestrictAddressFamilies=~AF_UNIX (a landrun hole that Linux 7.1 closes).
# COMPARATOR=auto (the default) uses builtin if bwrap can create user namespaces here, else
# standalone if .tools has been built, else stops and says what is missing. Every check runs
# before anything is fetched or built.
#
# Memory: `lake check` re-checks every declaration the default targets reach, all of Mathlib
# included; `lake comparator` exports only the 27 theorems and what they use (Lake/CLI/Check.lean).
# Re-check runs on 2026-11-01 reached 61.5 GB and 63.5 GB on the 62 GB Linux box and were
# OOM-killed, taking the session with them. So they run under a cap: MemoryMax=$(MEMORY_MAX), no
# swap, via systemd-run --user. A run the cap stops (status 137) is not a verdict: raise
# MEMORY_MAX on a machine with more RAM. Without systemd-run they refuse to run unless
# FORCE_UNCAPPED=1. `install` and `run` never run them.
.PHONY: comparator-tools comparator check comparator-local

MEMORY_MAX ?= 48G
FORCE_UNCAPPED ?=
TOOLS := $(CURDIR)/.tools
BWRAP := $(or $(COMPARATOR_BWRAP),bwrap)
COMPARATOR ?= auto

# The standalone tools, pinned. comparator: its last commit (2026-10-14; the repo is archived), whose
# lean-toolchain is v4.35.0, as ours. lean4export: the rev comparator's lake-manifest.json pins,
# built by the same `lake build`, so with the same Lean (the export format has to match the
# .olean files; lean4export's own master is on a newer Lean). landrun: main, as comparator asks
# (its go.mod wants Go 1.24; an older Go >= 1.21 fetches that toolchain by itself).
COMPARATOR_URL := https://github.com/leanprover/comparator
COMPARATOR_REV ?= 865edc14486c3388e9225daa971da8e157488c3e
LANDRUN_URL := https://github.com/Zouuup/landrun
LANDRUN_REV ?= ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a
COMPARATOR_BIN ?= $(TOOLS)/comparator/.lake/build/bin/comparator
LEAN4EXPORT_BIN ?= $(TOOLS)/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
LANDRUN_BIN ?= $(TOOLS)/bin/landrun

define need_linux
[ "$$(uname -s)" = Linux ] || { \
  echo "error: Comparator runs on Linux only. lake comparator and lake check sandbox with bubblewrap"; \
  echo "  and refuse to run elsewhere; the standalone comparator's sandbox, landrun, is Landlock (Linux)."; \
  echo "  On a Linux machine: git clone https://github.com/l-adic/zrdt && cd zrdt && make comparator"; \
  exit 2; }
endef

define cap_works
command -v systemd-run >/dev/null 2>&1 \
  && systemd-run --user --scope -q -p MemoryMax=64M -- true >/dev/null 2>&1
endef

# Refuse to start a MEMORY-HEAVY run that cannot be capped, unless FORCE_UNCAPPED=1.
define need_cap
if ! { $(cap_works); } && [ -z "$(FORCE_UNCAPPED)" ]; then \
  echo "error: systemd-run --user is not available, so this cannot run under a memory cap."; \
  echo "  Past runs of this re-check reached 61.5 GB and were OOM-killed. Run it on Linux with"; \
  echo "  systemd (MEMORY_MAX=... sets the cap), or set FORCE_UNCAPPED=1 to run it with no cap."; \
  exit 2; \
fi
endef

# $(call capped,command): run command under the memory cap (systemd-run --user --scope), or with
# no cap if FORCE_UNCAPPED=1 and there is no systemd-run; a failure is reported with the cap in mind.
define capped
$(need_cap); \
if $(cap_works); then \
  echo "memory cap: MemoryMax=$(MEMORY_MAX), MemorySwapMax=0 (systemd-run --user --scope)"; \
  systemd-run --user --scope -q -p MemoryMax=$(MEMORY_MAX) -p MemorySwapMax=0 -- $(1); \
else \
  echo "warning: systemd-run --user is not available; FORCE_UNCAPPED is set, so running with no memory cap"; \
  $(1); \
fi; \
rc=$$?; \
if [ $$rc -ne 0 ]; then \
  echo "exit status $$rc. If the memory cap stopped it (status 137, or a step that 'exited with 137'),"; \
  echo "  that is not a verdict: run it again with a larger MEMORY_MAX (now $(MEMORY_MAX)) on a machine with more RAM."; \
fi; \
exit $$rc
endef

define bwrap_works
$(BWRAP) --ro-bind / / --unshare-all --die-with-parent true >/dev/null 2>&1
endef

define need_bwrap
command -v $(BWRAP) >/dev/null 2>&1 || { \
  echo "error: bubblewrap ($(BWRAP)) not found; lake comparator / lake check run the project inside it."; \
  echo "  Debian/Ubuntu: sudo apt install bubblewrap   Fedora: sudo dnf install bubblewrap"; \
  echo "  or set COMPARATOR_BWRAP, or use the standalone comparator: make comparator-tools"; exit 2; }; \
$(bwrap_works) || { \
  echo "error: $(BWRAP) cannot create user namespaces here (on Ubuntu 23.10+, AppArmor restricts them)."; \
  echo "  Fix (root): give bwrap an AppArmor profile with 'userns,' (README, \"Running Comparator\"),"; \
  echo "  or, without root: make comparator-tools (needs Go for landrun), then make comparator again."; exit 2; }
endef

define need_standalone
for f in $(COMPARATOR_BIN) $(LEAN4EXPORT_BIN) $(LANDRUN_BIN); do [ -x $$f ] || { \
  echo "error: $$f is missing; build the standalone tools first: make comparator-tools"; \
  [ "$$f" != $(LANDRUN_BIN) ] || command -v go >/dev/null 2>&1 \
    || echo "  landrun needs Go 1.21 or newer: https://go.dev/dl/ (or: sudo apt install golang-go)"; \
  exit 2; }; done
endef

# $(call fetch_rev,url,rev,dir): a shallow checkout of exactly commit rev in dir (refetched if rev changes).
define fetch_rev
[ -d $(3)/.git ] || git init -q $(3); \
if [ "$$(git -C $(3) rev-parse -q --verify 'HEAD^{commit}' 2>/dev/null)" != "$(2)" ]; then \
  echo "fetch $(1) at $(2) into $(3)"; \
  git -C $(3) fetch -q --depth 1 $(1) $(2) \
    && git -C $(3) -c advice.detachedHead=false checkout -q FETCH_HEAD || exit 1; \
fi
endef

# The standalone comparator, run as its README says (systemd-run --user, RestrictAddressFamilies=~AF_UNIX,
# PATH passed in, from this directory), with the memory cap; a terminal gets --pty, else --pipe.
define run_standalone
echo "standalone comparator: $(COMPARATOR_BIN) (sandbox: landrun)"; \
if command -v systemd-run >/dev/null 2>&1 && systemd-run --user --pipe --wait --collect -q \
     -p MemoryMax=64M -p RestrictAddressFamilies=~AF_UNIX -- true </dev/null >/dev/null 2>&1; then \
  if [ -t 0 ] && [ -t 1 ]; then io=--pty; else io=--pipe; fi; \
  echo "systemd-run --user $$io: RestrictAddressFamilies=~AF_UNIX, MemoryMax=$(MEMORY_MAX), MemorySwapMax=0"; \
  systemd-run --user $$io --wait --collect -q \
    -p RestrictAddressFamilies=~AF_UNIX -p MemoryMax=$(MEMORY_MAX) -p MemorySwapMax=0 \
    -E PATH="$$PATH" -E COMPARATOR_LANDRUN=$(LANDRUN_BIN) -E COMPARATOR_LEAN4EXPORT=$(LEAN4EXPORT_BIN) \
    $${ELAN_HOME:+-E ELAN_HOME="$$ELAN_HOME"} --working-directory "$(CURDIR)" -- \
    lake env $(COMPARATOR_BIN) comparator.json; \
  rc=$$?; \
  [ $$rc -eq 0 ] || echo "exit status $$rc. If the memory cap (MEMORY_MAX=$(MEMORY_MAX)) stopped it, that is not a verdict: raise MEMORY_MAX on a machine with more RAM."; \
  exit $$rc; \
elif [ -n "$(FORCE_UNCAPPED)" ]; then \
  echo "warning: systemd-run --user is not available: no RestrictAddressFamilies=~AF_UNIX (comparator's README asks for it until Linux 7.1) and no memory cap"; \
  COMPARATOR_LANDRUN=$(LANDRUN_BIN) COMPARATOR_LEAN4EXPORT=$(LEAN4EXPORT_BIN) lake env $(COMPARATOR_BIN) comparator.json; \
else \
  echo "error: systemd-run --user is not available: comparator's README asks for its RestrictAddressFamilies=~AF_UNIX"; \
  echo "  guard, and the memory cap needs it too. Set FORCE_UNCAPPED=1 to run without both."; \
  exit 2; \
fi
endef

# Every module of ours: the spec and proofs (Crdt) and the shipped code (core/Zrdt).
OWN_MODULES = $(shell find Crdt core/Zrdt -name '*.lean' | sed -e 's|^core/||' -e 's|\.lean$$||' -e 's|/|.|g' | sort)

comparator-tools: ## Build the standalone comparator, its lean4export and landrun (needs Go) into .tools/; runs nothing
	@$(need_lake)
	@command -v git >/dev/null 2>&1 || { echo "error: git is needed to fetch the tools"; exit 1; }
	@mkdir -p $(TOOLS)/bin
	@$(call fetch_rev,$(COMPARATOR_URL),$(COMPARATOR_REV),$(TOOLS)/comparator)
	@cmp -s lean-toolchain $(TOOLS)/comparator/lean-toolchain || { \
	  echo "error: $(TOOLS)/comparator is on $$(cat $(TOOLS)/comparator/lean-toolchain), this project on $$(cat lean-toolchain)."; \
	  echo "  lean4export must be built with this project's Lean; pick a COMPARATOR_REV on the same toolchain."; exit 1; }
	cd $(TOOLS)/comparator && lake build lean4export comparator
	ln -sf $(COMPARATOR_BIN) $(TOOLS)/bin/comparator
	ln -sf $(LEAN4EXPORT_BIN) $(TOOLS)/bin/lean4export
	@if command -v go >/dev/null 2>&1; then \
	  $(call fetch_rev,$(LANDRUN_URL),$(LANDRUN_REV),$(TOOLS)/landrun); \
	  echo "cd $(TOOLS)/landrun && go build -o $(LANDRUN_BIN) ./cmd/landrun"; \
	  ( cd $(TOOLS)/landrun && GOTOOLCHAIN="$${GOTOOLCHAIN:-auto}" go build -o $(LANDRUN_BIN) ./cmd/landrun ) || exit 1; \
	  echo "comparator-tools: done. $(TOOLS)/bin: comparator, lean4export, landrun."; \
	  echo "make comparator uses them when bwrap cannot sandbox here (or with COMPARATOR=standalone)."; \
	else \
	  echo "comparator-tools: built comparator and lean4export, but NOT landrun (its sandbox): go not found."; \
	  echo "  Get Go 1.21 or newer: https://go.dev/dl/ (or: sudo apt install golang-go, brew install go),"; \
	  echo "  then run make comparator-tools again."; \
	fi

comparator: ## MEMORY-HEAVY, Linux only (capped, MEMORY_MAX=48G): judge Api.lean against Comparator/Challenge.lean
	@$(need_lake)
	@$(need_linux)
	@mode=$(COMPARATOR); \
	if [ "$$mode" = auto ]; then \
	  if $(bwrap_works); then mode=builtin; \
	  elif [ -x $(COMPARATOR_BIN) ] && [ -x $(LEAN4EXPORT_BIN) ] && [ -x $(LANDRUN_BIN) ]; then mode=standalone; \
	    echo "$(BWRAP) cannot create user namespaces here; using the standalone comparator (.tools)"; \
	  elif [ -x $(COMPARATOR_BIN) ] && [ -x $(LEAN4EXPORT_BIN) ]; then \
	    echo "error: $(BWRAP) cannot create user namespaces here, and the standalone comparator is built but"; \
	    echo "  landrun, its sandbox, is not (no Go when make comparator-tools ran). Install Go 1.21 or newer"; \
	    echo "  (https://go.dev/dl/, or: sudo apt install golang-go), then: make comparator-tools && make comparator"; \
	    exit 2; \
	  else mode=builtin; fi; \
	fi; \
	case $$mode in \
	  builtin) $(need_bwrap);; \
	  standalone) $(need_standalone);; \
	  *) echo "error: COMPARATOR=$$mode: use auto, builtin or standalone"; exit 2;; \
	esac; \
	$(need_cap); \
	echo "lake exe cache get   (Mathlib's prebuilt files: the sandboxed build has no network)"; \
	lake exe cache get || exit 1; \
	case $$mode in \
	  builtin) \
	    echo "built-in comparator: lake comparator --config comparator.json"; \
	    $(call capped,lake comparator --config comparator.json);; \
	  standalone) \
	    $(run_standalone);; \
	esac

check: ## MEMORY-HEAVY (re-checks all of Mathlib; capped), Linux only: replay the default targets with `lake check`
	@$(need_lake)
	@$(need_linux)
	@$(need_bwrap)
	@$(need_cap)
	lake exe cache get
	@$(call capped,lake check)

comparator-local: ## MEMORY-HEAVY (capped), no sandbox, NOT the verdict: statements + axioms, then leanchecker
	@$(need_cap)
	lake build Comparator.Challenge $(OWN_MODULES)
	@$(call capped,lake env lean --run scripts/CompareStatements.lean)
	@$(call capped,lake env leanchecker $(OWN_MODULES))
