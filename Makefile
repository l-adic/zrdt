.DEFAULT_GOAL := help
.PHONY: help install run graph

help: ## Show this help (targets are documented by the "##" comment on their line)
	@grep -E '^[a-zA-Z0-9_-]+:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "}; {printf "  \033[1m%-10s\033[0m %s\n", $$1, $$2}'

install: ## Fetch the Mathlib build cache and build the project (runs the axiom gate)
	lake exe cache get
	lake build

run: ## Run the axiom gate executable
	lake exe axiom_check

graph: ## Import graph of this project's own modules (no Mathlib) -> docs/imports.dot [+ .svg]
	mkdir -p docs
	lake exe graph --to Crdt docs/imports.dot
	@command -v dot >/dev/null 2>&1 && dot -Tsvg docs/imports.dot -o docs/imports.svg && echo "wrote docs/imports.svg" || echo "graphviz not installed; wrote docs/imports.dot only"

# zrdtd, its vectors and its closure check (docs/PLAN.md §4 C, §6 rungs 2a and 6). These run
# inside core/ (package zrdt-core: Init and Std only) and never build Mathlib.
.PHONY: zrdtd vectors closure

ZRDTD := core/.lake/build/bin/zrdtd

zrdtd: ## Build the zrdtd daemon (core/, no Mathlib) -> core/.lake/build/bin/zrdtd
	cd core && lake build zrdtd

vectors: ## Regenerate vectors/vectors.json from core/Zrdt/Vectors.lean
	mkdir -p vectors
	cd core && lake build && lake env lean --run Zrdt/Vectors.lean > ../vectors/vectors.json.tmp
	mv vectors/vectors.json.tmp vectors/vectors.json

closure: ## Check the linked zrdtd: only Init, Std, zrdt-core (and runtime libuv) initializers, no lean_initialize; silent if OK
	@cd core && lake -q build zrdtd
	@bad=$$(nm $(ZRDTD) | awk '{print $$NF}' | sed 's/^_//' \
	  | grep -E '^((runtime_|meta_)?initialize_[A-Za-z]|lean_initialize$$)|[Mm]athlib' \
	  | grep -vE '^(runtime_|meta_)?initialize_(Init|Std|zrdt_x2dcore)(_|$$)|^initialize_libuv$$' \
	  | sort -u); \
	if [ -n "$$bad" ]; then \
	  echo "closure check failed: $(ZRDTD) links $$(echo "$$bad" | wc -l) other initializers, e.g.:"; \
	  echo "$$bad" | head -10; exit 1; fi
