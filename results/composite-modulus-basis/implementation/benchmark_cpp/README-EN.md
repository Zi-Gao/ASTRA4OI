# Standardized C++ performance comparison

[中文](README.md) · [Artifact entry](../../README-EN.md)

**[Completed performance results](../../docs/en/cpp-benchmark-results.md)**: 36 datasets, O2/native controls, raw repetitions and resource-limit outcomes.

The workload is static batched interval membership: identical input and ordered answers for every candidate; offline query reordering is allowed. Supported domain: `2 <= m < 2^32`, `1 <= d <= 256`. Ordinary products use 64 bits; reciprocal reduction and Bezout combinations use compiler `__int128`. Clang/GCC on macOS/Linux and Python 3.10+ are required, with no third-party packages.

## Implementations

| Name | Implementation | Scope |
| --- | --- | --- |
| `timestamp-basic` | STL priority queue, owning row objects, full-row modular passes | Readable C++ implementation of the paper algorithm |
| `timestamp-fast` | Flat pivots, k reusable task buffers, in-place suffix updates, exact reciprocal reduction; masks/ctz/Newton unit inverses for powers of two | Optimized implementation, not a claim of absolute hardware optimality |
| `closure-prototype` | FIFO propagation of p*pivot after every write | Port of this project's historical prototype; internal ablation |
| `howell-rebuild` | Rebuild saturated triangular generators for each interval | Factorization-free |
| `howell-segment` | Segment tree of mergeable summaries | Factorization-free |
| `howell-sparse` | Sparse table; merge two possibly overlapping blocks | Factorization-free |
| `field-timestamp` | Independent field implementation without power levels or task queues, using the same fast arithmetic | Prime moduli only |
| `xor-packed` | 64-bit packed XOR timestamp basis | m=2, d≤64 |

The three Howell-style candidates share a locally implemented saturated-echelon kernel. They are not tuned canonical-form library implementations and do not use fast matrix multiplication. Entries above pivots are not canonically reduced, so the output is not claimed to be canonical Howell form. Full-module detection permits early exits. Their unit-pivot steps over powers of two use the same Newton inverse; the baselines are not deliberately weakened.

Design references: [modular linear algebra](https://cs.uwaterloo.ca/~astorjoh/esa.pdf), [Howellize annihilator closure](https://research.cs.wisc.edu/wpis/papers/TR1792-R1.pdf), and [a first-hand field timestamp implementation](https://www.cnblogs.com/Xun-Xiaoyao/p/17275653.html). The code is independently written; the segment-tree/sparse-table wrappers are this project's constructions, not interval results attributed to those papers.

## Correctness before timing

`verify.py` checks every applicable candidate against exhaustive small sequences/intervals/targets, independent integer-lattice membership, and the Python reference. Cases include noncanonical signed residues, moduli near `2^32`, deep powers, coupled low rank, zeros, duplicates, empty query batches, and the top packed bit. Basic/fast task counters must agree and satisfy the operation allowances.

`arithmetic_test.cpp` compares optimized arithmetic against native `%` and gcd/inverse identities, including full-width 64-bit dividends and 32-bit boundaries. Checks remain active under `-DNDEBUG`.

Each performance dataset has eight fixed short-interval lattice probes. Every odd-indexed target is a constructed YES; coupled/nonunit datasets also force every even-indexed target to be NO. All completed outputs are cross-compared by SHA-256, not merely YES counts. Neither these C++ implementations nor the Howell-style kernel are source-refined by the Lean development.

## Measurement protocol

- One process per candidate/input, identical compiler flags for all candidates.
- Primary `solve_seconds` includes structure construction, offline bucketing, queries, internal allocations and destruction; excludes generation, input parsing, output, and oracle work.
- `program_seconds` additionally includes parsing, supplied-factor validation and output. Runner wall time includes monitoring granularity and is unsuitable for ranking very short programs.
- Default one warmup and five measured repetitions; median, min/max and every raw run are retained. Candidate order is deterministically shuffled each round, with serial execution.
- RSS is whole-process high-water memory, including inputs and answers. The sampled wall/RSS watchdog can overshoot briefly; final high-water usage is checked too.
- Timeouts, memory failures and unsupported candidates remain visible. No exact speedup is inferred from a timeout threshold. Wrong answers stop the run.
- This offline workload does not save historical timestamp snapshots; do not infer historical-online memory costs from it.
- Factorizations are supplied to timestamp methods and not passed to Howell methods. Factorization algorithms are not timed. Both timestamp implementations retain lightweight operation counters.

`portable` uses `-O2 -DNDEBUG`; `native` uses `-O3 -DNDEBUG -march=native`, uniformly across candidates. `sanitize` enables address/undefined-behavior checks; `ubsan` enables only undefined-behavior checks. Neither is a release-performance configuration. CPU affinity/frequency and other host workloads are not controlled; rerun quietly before publication.

Apple Clang 17 AddressSanitizer deadlocked before main on this macOS 26.6.2 host; ASan coverage is unavailable, as recorded in the [failure log](../../artifacts/cpp-benchmark/sanitizer-smoke/validation-failure.txt). See the independent UBSan pipeline's [validation report](../../artifacts/cpp-benchmark/ubsan-final/report.md). Instrumented timings are diagnostic only.

## Datasets and commands

`smoke` checks the small end-to-end pipeline. `standard` covers binary/prime/square/deep-power/odd-power/multi-prime moduli, 32-bit boundaries and structured data. `scaling` varies n, d, k, w and q separately. `stress` includes n=100000, q=500000 or d=128 resource-limit cases.

Intervals mix singletons, short/dimension-scale intervals and arbitrary lengths. Known-positive and structured-negative targets prevent exclusively random full-rank long intervals from reducing to all YES. Distributions, length histograms and answer fractions are recorded. The valuation ladder is a structured stress family, not a proved worst case.

From the artifact root:

```sh
make cpp-test
make benchmark-cpp
make benchmark-cpp-native
make benchmark-cpp-stress
python3 implementation/benchmark_cpp/run.py --profile scaling --tuning native
```

Custom budgets and subsets:

```sh
python3 implementation/benchmark_cpp/run.py --profile standard --tuning native --repeats 5 --timeout 10 --memory-mib 512
python3 implementation/benchmark_cpp/run.py --profile stress --tuning native --cases n100k-d64-square --repeats 3
python3 implementation/benchmark_cpp/run.py --profile smoke --tuning sanitize --repeats 1 --warmups 0 --quick-verification
```

Use `--algorithms timestamp-basic,timestamp-fast,howell-segment` for a subset, `--seed` for another dataset seed, and `CXX=clang++` / `CXX=g++` to select the compiler. Each default output directory has a UTC timestamp; `--output` selects a directory, without silently replacing existing results.

After interruption, repeat the original command and output directory with `--resume`. Completed cases are preserved; unfinished cases restart after source/generator fingerprints, settings, compiler and hardware checks. Interrupted records remain available. Do not launch multiple runners against the same output directory concurrently.

`artifacts/cpp-benchmark/` contains Markdown reports, raw JSON, verification logs, source/data fingerprints, compiler details and reproduction commands. Large inputs are reproducibly regenerated and deleted after successful benchmarking; binaries and temporary files live under ignored `build/`.

Standalone C++ uses the Python program's input format:

```sh
build/cpp-benchmark/bench --algorithm timestamp-fast --factors 2:2 < implementation/examples/example.in
build/cpp-benchmark/bench --algorithm howell-segment < implementation/examples/example.in
```

The actual factors must match the input modulus. Answers go to stdout; one JSON metrics line goes to stderr. Do not combine the streams when consuming judge answers.
