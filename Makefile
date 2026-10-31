.PHONY: install run

install:
	lake exe cache get
	lake build

run:
	lake exe axiom_check
