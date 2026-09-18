PYTHON ?= python3
LATEXMK ?= latexmk
CXX ?= c++

.PHONY: test test-large formal core map check paper benchmark cpp-test benchmark-cpp benchmark-cpp-native benchmark-cpp-stress

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

cpp-test:
	mkdir -p build/cpp-benchmark
	$(CXX) -std=c++17 -O2 -DNDEBUG -Wall -Wextra implementation/benchmark_cpp/main.cpp -o build/cpp-benchmark/bench
	$(CXX) -std=c++17 -O2 -DNDEBUG -Wall -Wextra implementation/benchmark_cpp/arithmetic_test.cpp -o build/cpp-benchmark/arithmetic_test
	build/cpp-benchmark/arithmetic_test
	$(PYTHON) implementation/benchmark_cpp/verify.py --binary build/cpp-benchmark/bench --output build/cpp-benchmark/verification.json

benchmark-cpp:
	CXX="$(CXX)" $(PYTHON) implementation/benchmark_cpp/run.py --profile standard

benchmark-cpp-native:
	CXX="$(CXX)" $(PYTHON) implementation/benchmark_cpp/run.py --profile standard --tuning native

benchmark-cpp-stress:
	CXX="$(CXX)" $(PYTHON) implementation/benchmark_cpp/run.py --profile stress --tuning native
