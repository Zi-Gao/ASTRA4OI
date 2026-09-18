# C++ interval-membership benchmark

UTC: 2026-09-18T10:30:42.998198+00:00

All algorithms consume identical input files and emit identical ordered answers on completed runs.
Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.
This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.
RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.

- Host: Apple M3 Pro; Darwin 25.6.0
- Compiler: `Apple clang version 17.0.0 (clang-1700.6.3.2)`
- Flags: `-std=c++17 -Wall -Wextra -O3 -DNDEBUG -march=native`
- Profile: `stress`; seed 20260917; warmups=1; measured repeats=3
- Per-process wall timeout: 8.0 s; RSS budget: 512 MiB (sampled watchdog plus final high-water check)
- Correctness gate: 2,741,761 C++ membership assertions; exact arithmetic self-test passed.
- Howell candidates are local saturated-echelon implementations, not a tuned canonical-form library or a fast-matrix-multiplication implementation.
- closure-prototype is an internal historical ablation, not independent published prior art.
- No CPU pinning, frequency locking, or exclusive-machine guarantee; rerun on a quiet machine for publication.

[Raw measurements and dataset manifests](results.json)

Resumed 1 time(s): completed cases were preserved; interrupted cases were restarted. Partial runs and resume environments remain in results.json.

## Results

Fast/basic is a matched speed ratio, not a comparison against the fastest competing method. A timeout is not an exact runtime.

| Case | n / d / q | m / K / w | Algorithm | Solve median [min, max] s | Program median s | Peak RSS MiB | YES % |
| --- | --- | --- | --- | --- | --- | --- | --- |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | howell-rebuild | 2.795674 [2.775264, 2.938255] | 2.854084 | 56.5 | 68.9 |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | timestamp-fast | 0.423938 [0.409162, 0.440941] | 0.488649 | 59.7 | 68.9 |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | howell-segment | memory_limit | — | — | — |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | closure-prototype | 1.304888 [1.294184, 1.338830] | 1.366885 | 59.8 | 68.9 |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | timestamp-basic | 1.223960 [1.136614, 1.361573] | 1.285262 | 59.7 | 68.9 |
| n100k-d64-square | 100000 / 64 / 100000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | field-timestamp | unsupported | — | — | — |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | xor-packed | unsupported | — | — | — |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | howell-rebuild | 0.863081 [0.862085, 0.874850] | 1.000968 | 32.0 | 68.9 |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | timestamp-fast | 4.482031 [4.436415, 4.606100] | 4.621276 | 35.2 | 68.9 |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | howell-segment | 1.186406 [1.132883, 1.337519] | 1.321690 | 347.5 | 68.9 |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | closure-prototype | timeout | — | — | — |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | timestamp-basic | timeout | — | — | — |
| n100k-deep-power | 100000 / 32 / 100000 | 1073741824 / 30 / 1 | howell-sparse | memory_limit | — | — | — |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | field-timestamp | unsupported | — | — | — |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | xor-packed | unsupported | — | — | — |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | howell-rebuild | 1.771882 [1.757124, 1.913626] | 1.885512 | 32.0 | 68.7 |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | timestamp-fast | 0.877554 [0.876225, 1.046960] | 0.982494 | 35.2 | 68.7 |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | howell-segment | 2.533193 [2.429944, 2.557130] | 2.639677 | 358.3 | 68.7 |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | closure-prototype | 2.129781 [2.052810, 2.198343] | 2.237530 | 35.2 | 68.7 |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | timestamp-basic | 2.183865 [2.168105, 2.325253] | 2.304726 | 35.2 | 68.7 |
| n100k-many-primes | 100000 / 32 / 100000 | 9699690 / 8 / 8 | howell-sparse | memory_limit | — | — | — |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | howell-rebuild | 2.813191 [2.629216, 2.864983] | 2.907770 | 83.2 | 69.0 |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | timestamp-fast | 0.204993 [0.202676, 0.205462] | 0.300661 | 87.8 | 69.0 |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | howell-segment | 2.581938 [2.573524, 2.600083] | 2.678391 | 155.6 | 69.0 |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | closure-prototype | 0.331041 [0.329130, 0.485462] | 0.433341 | 87.8 | 69.0 |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | timestamp-basic | 0.386048 [0.374044, 0.397158] | 0.488977 | 87.9 | 69.0 |
| q500k-square | 20000 / 32 / 500000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | howell-rebuild | 3.481025 [3.458559, 3.645115] | 3.507763 | 22.4 | 68.2 |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | timestamp-fast | 0.237878 [0.235901, 0.238769] | 0.262730 | 23.1 | 68.2 |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | howell-segment | 2.674847 [2.529395, 2.720387] | 2.701822 | 329.6 | 68.2 |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | closure-prototype | 0.942997 [0.911321, 1.063626] | 0.967581 | 23.2 | 68.2 |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | timestamp-basic | 0.806961 [0.766930, 0.825813] | 0.830936 | 23.2 | 68.2 |
| dimension-128 | 20000 / 128 / 20000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |

## Matched implementation comparison

| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |
| --- | --- | --- | --- |
| n100k-d64-square | 2.89x | 0.15x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| n100k-deep-power | — | 5.19x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| n100k-many-primes | 2.49x | 0.50x (howell-rebuild; <1 means timestamp-fast is faster) | fast timing CV > 10% |
| q500k-square | 1.88x | 0.08x (howell-segment; <1 means timestamp-fast is faster) | — |
| dimension-128 | 3.39x | 0.09x (howell-segment; <1 means timestamp-fast is faster) | — |

## Reproduction

Run from the result directory:

```sh
python3 implementation/benchmark_cpp/run.py --profile stress --tuning native --repeats 3 --warmups 1 --seed 20260917 --timeout 8.0 --memory-mib 512 --algorithms timestamp-basic,timestamp-fast,closure-prototype,howell-rebuild,howell-segment,howell-sparse,field-timestamp,xor-packed
```

Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.
Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.
Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.
Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.
A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.
