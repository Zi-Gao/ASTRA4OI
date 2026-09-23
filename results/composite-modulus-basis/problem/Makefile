PYTHON ?= python3
CXX ?= c++
BUILD := ../build/problem
SOLUTION_NAMES := timestamp-basic timestamp-fast closure-prototype howell-rebuild howell-segment howell-sparse field-timestamp xor-packed dimension-one-gcd prefix-howell
SOLUTION_BINS := $(addprefix $(BUILD)/,$(SOLUTION_NAMES))

.PHONY: all solutions data check quick sanitize compare

all: $(BUILD)/std $(BUILD)/brute solutions

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/std: std.cpp | $(BUILD)
	$(CXX) -std=c++17 -O2 -DNDEBUG -Wall -Wextra -Wpedantic $< -o $@

$(BUILD)/brute: brute.cpp | $(BUILD)
	$(CXX) -std=c++17 -O2 -DNDEBUG -Wall -Wextra -Wpedantic $< -o $@

solutions: $(SOLUTION_BINS)

$(SOLUTION_BINS): $(BUILD)/%: solutions/%.cpp solutions/runner.hpp ../implementation/benchmark_cpp/algorithms.hpp | $(BUILD)
	$(CXX) -std=c++17 -O2 -DNDEBUG -Wall -Wextra -Wpedantic $< -o $@

data:
	$(PYTHON) gen.py

check:
	CXX="$(CXX)" $(PYTHON) verify.py

quick:
	CXX="$(CXX)" $(PYTHON) verify.py --quick --skip-regeneration

sanitize:
	CXX="$(CXX)" $(PYTHON) verify.py --quick --sanitize --skip-regeneration

compare:
	CXX="$(CXX)" $(PYTHON) benchmark_solutions.py
