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
