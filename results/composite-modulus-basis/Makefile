PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: test test-large formal core map check paper benchmark

test:
	$(PYTHON) implementation/test_solver.py

test-large:
	$(PYTHON) implementation/test_solver.py --suite large

core:
	$(PYTHON) formal/verify.py

formal:
	$(PYTHON) formal/verify.py --regression

map:
	$(PYTHON) formal/sync_paper.py
	$(PYTHON) formal/sync_paper.py --check

check:
	$(PYTHON) formal/sync_paper.py --check
	$(PYTHON) paper/check_artifact.py

paper: map
	cd paper && $(LATEXMK) -xelatex -interaction=nonstopmode -halt-on-error -outdir=build main-zh.tex
	cd paper && $(LATEXMK) -xelatex -interaction=nonstopmode -halt-on-error -outdir=build main-en.tex
	mkdir -p paper/output/pdf
	cp paper/build/main-zh.pdf paper/output/pdf/paper-zh.pdf
	cp paper/build/main-en.pdf paper/output/pdf/paper-en.pdf

benchmark:
	$(PYTHON) implementation/benchmark.py
