# C++ constant-factor tuning: paired before/after comparison

[中文](../zh/constant-tuning.md)

Against `timestamp-fast` at commit `9a0fb9e`, median whole-solve time decreased on all 36 native datasets, giving **1.08–2.16x** speedups. These are old-fast versus new-fast comparisons, not comparisons against the basic implementation or Howell baselines.

Apple M3 Pro / Apple Clang 17. Native: `-O3 -DNDEBUG -march=native`; portable: `-O2 -DNDEBUG`; C++17 throughout. One warmup, five standard repetitions and three scaling/stress repetitions; randomized version order within each round, serial execution. Solve time includes bucketing, construction, queries, internal allocation and cache initialization, but excludes I/O. CPU frequency and background load were not controlled; small differences do not establish cross-machine guarantees.

## Retained optimizations

1. Odd-prime-power divisibility uses multiplication by inverses modulo `2^32` and a threshold comparison. Exact quotients use one multiplication; powers of two use shifts. Hot valuation/quotient divisions are removed.
2. Unit inversion uses 32-bit remainders and signed 64-bit coefficients in extended Euclid. Small odd moduli cache inverses lazily, with a multiplication table for moduli at most 32. Each component adds at most 256 KiB for inverses and 4 KiB for products, including their setup in solve time.
3. Power-of-two suffix loops use 32-bit wrapping multiply/subtract and masks. Empty-slot and occupied-slot normalization have separate loops; the known pivot coordinate is assigned directly.
4. Initial tasks already form a heap. A displaced successor has an older timestamp, requiring only one root sift-down instead of a pop followed by a push.
5. Unit pivots certify the full module: when every column has one, their minimum timestamp certifies all earlier left endpoints. The certificate is invalidated on unit-pivot writes and recomputed lazily; rank-deficient modules cannot trigger it.

Insertion counts (`visits / reductions / writes / pops / max_pending`) match the old version exactly. Query shortcuts are outside these insertion counts. The API, supported domain and general complexity bounds are unchanged. No source refinement from the C++ machine-arithmetic optimizations to Lean is claimed.

## Standard: native and O2

| Dataset | Old native ms | New native ms | Speedup | Old O2 ms | New O2 ms | Speedup |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-d64 | 36.39 | 25.68 | 1.42x | 37.36 | 25.32 | 1.48x |
| prime-d32 | 34.36 | 28.42 | 1.21x | 36.72 | 28.80 | 1.27x |
| square-d32 | 29.52 | 24.68 | 1.20x | 33.27 | 24.74 | 1.34x |
| deep-power-d24 | 173.24 | 149.03 | 1.16x | 184.17 | 147.06 | 1.25x |
| odd-power-d24 | 236.25 | 128.35 | 1.84x | 248.04 | 129.44 | 1.92x |
| crt-d32 | 66.18 | 46.85 | 1.41x | 71.81 | 46.24 | 1.55x |
| many-primes-d24 | 86.46 | 40.30 | 2.15x | 94.30 | 41.71 | 2.26x |
| word-boundary-d32 | 36.95 | 30.52 | 1.21x | 39.12 | 30.60 | 1.28x |
| composite-boundary-d24 | 69.30 | 37.55 | 1.85x | 76.89 | 39.04 | 1.97x |
| coupled-crt-d32 | 62.62 | 49.72 | 1.26x | 68.04 | 49.75 | 1.37x |
| nonunit-power-d24 | 157.08 | 131.07 | 1.20x | 172.21 | 131.98 | 1.30x |
| valuation-ladder-d24 | 11.71 | 9.94 | 1.18x | 13.82 | 11.70 | 1.18x |
| zeros-duplicates-d32 | 23.98 | 16.37 | 1.46x | 25.12 | 15.65 | 1.60x |

## Stress

| Case | Before ms | After ms | Speedup | Peak RSS before / after MiB |
| --- | ---: | ---: | ---: | ---: |
| n100k-d64-square | 424.73 | 331.61 | 1.28x | 59.70 / 59.69 |
| n100k-deep-power | 4466.28 | 3670.41 | 1.22x | 35.31 / 35.31 |
| n100k-many-primes | 911.47 | 459.12 | 1.99x | 35.20 / 35.20 |
| q500k-square | 222.41 | 138.47 | 1.61x | 87.80 / 87.78 |
| dimension-128 | 252.73 | 187.83 | 1.35x | 23.12 / 23.12 |

## Scaling

| Case | Before ms | After ms | Speedup | Peak RSS before / after MiB |
| --- | ---: | ---: | ---: | ---: |
| dimension-8 | 3.27 | 2.79 | 1.17x | 3.31 / 3.33 |
| dimension-16 | 6.51 | 5.12 | 1.27x | 4.03 / 4.05 |
| dimension-32 | 13.99 | 11.06 | 1.26x | 5.50 / 5.50 |
| dimension-64 | 39.82 | 28.09 | 1.42x | 8.47 / 8.47 |
| exponent-1 | 4.93 | 3.64 | 1.35x | 4.81 / 4.81 |
| exponent-2 | 9.78 | 7.99 | 1.23x | 4.81 / 4.81 |
| exponent-4 | 21.52 | 19.23 | 1.12x | 4.83 / 4.81 |
| exponent-8 | 50.58 | 45.59 | 1.11x | 4.84 / 4.83 |
| exponent-16 | 119.18 | 101.61 | 1.17x | 4.88 / 4.88 |
| exponent-30 | 239.31 | 205.18 | 1.17x | 4.92 / 4.91 |
| queries-1000 | 9.61 | 8.88 | 1.08x | 2.98 / 2.98 |
| queries-8000 | 11.56 | 9.90 | 1.17x | 4.19 / 4.19 |
| queries-64000 | 30.27 | 19.62 | 1.54x | 13.44 / 13.44 |
| length-1000 | 4.96 | 2.96 | 1.68x | 4.39 / 4.38 |
| length-64000 | 81.91 | 71.81 | 1.14x | 15.03 / 15.03 |
| components-2 | 11.16 | 7.36 | 1.52x | 4.83 / 4.81 |
| components-4 | 25.10 | 14.27 | 1.76x | 4.83 / 4.83 |
| components-8 | 57.93 | 26.77 | 2.16x | 4.84 / 4.83 |

## Validation and records

Native, O2 and UBSan builds each passed **2,741,761 independent membership assertions**, including exhaustive enumeration, integer-lattice oracles, the Python reference and input boundaries. Additional arithmetic regressions cover dimension 256, `2^31`, `3^20`, `5^13`, `65521^2`, a prime near `2^32`, small product tables, certificate invalidation and task counts. UBSan reported no undefined behavior.

All timed runs compare complete-output SHA-256, five insertion counters and eight independent lattice probes per dataset. Raw JSON retains every timing, program time, RSS, dataset parameters and input/binary/source hashes. ASan could not start reliably in the previously recorded host environment; no ASan coverage is claimed here.

The original 36-case cross-algorithm report remains a historical snapshot. Do not divide new timings by previously measured Howell timings to claim fresh cross-algorithm speedups.

## Reproduction

From the artifact root, for native standard cases:

```sh
mkdir -p build/constant-tuning/baseline
git show 9a0fb9e:results/composite-modulus-basis/implementation/benchmark_cpp/main.cpp > build/constant-tuning/baseline/main.cpp
git show 9a0fb9e:results/composite-modulus-basis/implementation/benchmark_cpp/algorithms.hpp > build/constant-tuning/baseline/algorithms.hpp
clang++ -std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra build/constant-tuning/baseline/main.cpp -o build/constant-tuning/before
clang++ -std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra implementation/benchmark_cpp/main.cpp -o build/constant-tuning/after
python3 implementation/benchmark_cpp/verify.py --binary build/constant-tuning/after
python3 implementation/benchmark_cpp/compare_versions.py --before build/constant-tuning/before --after build/constant-tuning/after --profile standard --repeats 5 --before-label 9a0fb9e --build-flags='-std=c++17 -O3 -DNDEBUG -march=native -Wall -Wextra' --output build/constant-tuning/reproduced-standard.json
```

Use `--profile scaling` or `stress`, `--repeats 3`, and a fresh output path for other profiles. For portable comparisons, compile both binaries with `-O2 -DNDEBUG` and update `--build-flags`. Run `make cpp-test` for the complete O2 correctness gate. Output files must not already exist.

- [Native standard](../../artifacts/cpp-benchmark/constant-tuning/standard.json)
- [O2 standard](../../artifacts/cpp-benchmark/constant-tuning/standard-o2.json)
- [Scaling](../../artifacts/cpp-benchmark/constant-tuning/scaling.json)
- [Stress](../../artifacts/cpp-benchmark/constant-tuning/stress.json)
- [Native verification](../../artifacts/cpp-benchmark/constant-tuning/verification.txt)
- [O2 verification](../../artifacts/cpp-benchmark/constant-tuning/verification-o2.txt)
- [UBSan verification](../../artifacts/cpp-benchmark/constant-tuning/verification-ubsan.txt)
- [UBSan arithmetic](../../artifacts/cpp-benchmark/constant-tuning/arithmetic-ubsan.txt)
- [Build provenance](../../artifacts/cpp-benchmark/constant-tuning/provenance.json)
