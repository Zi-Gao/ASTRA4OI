# C++ interval-membership benchmark

UTC: 2026-09-18T10:26:20.915386+00:00

All algorithms consume identical input files and emit identical ordered answers on completed runs.
Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.
This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.
RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.

- Host: Apple M3 Pro; Darwin 25.6.0
- Compiler: `Apple clang version 17.0.0 (clang-1700.6.3.2)`
- Flags: `-std=c++17 -Wall -Wextra -O1 -g -fsanitize=undefined -fno-sanitize-recover=all -fno-omit-frame-pointer`
- Profile: `smoke`; seed 20260917; warmups=0; measured repeats=1
- Per-process wall timeout: 15.0 s; RSS budget: 1024 MiB (sampled watchdog plus final high-water check)
- Correctness gate: 7,732 C++ membership assertions; exact arithmetic self-test passed.
- Howell candidates are local saturated-echelon implementations, not a tuned canonical-form library or a fast-matrix-multiplication implementation.
- closure-prototype is an internal historical ablation, not independent published prior art.
- No CPU pinning, frequency locking, or exclusive-machine guarantee; rerun on a quiet machine for publication.

[Raw measurements and dataset manifests](results.json)

## Results

Fast/basic is a matched speed ratio, not a comparison against the fastest competing method. A timeout is not an exact runtime.

| Case | n / d / q | m / K / w | Algorithm | Solve median [min, max] s | Program median s | Peak RSS MiB | YES % |
| --- | --- | --- | --- | --- | --- | --- | --- |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | timestamp-basic | 0.000372 [0.000372, 0.000372] | 0.000640 | 3.7 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | howell-rebuild | 0.001920 [0.001920, 0.001920] | 0.002106 | 3.6 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | howell-segment | 0.002879 [0.002879, 0.002879] | 0.003155 | 3.9 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | howell-sparse | 0.004982 [0.004982, 0.004982] | 0.005250 | 5.3 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | xor-packed | 0.000085 [0.000085, 0.000085] | 0.000339 | 3.6 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | closure-prototype | 0.000404 [0.000404, 0.000404] | 0.001571 | 3.8 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | field-timestamp | 0.000243 [0.000243, 0.000243] | 0.000609 | 3.8 | 59.8 |
| binary | 128 / 32 / 256 | 2 / 1 / 1 | timestamp-fast | 0.000238 [0.000238, 0.000238] | 0.000424 | 3.7 | 59.8 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| square | 160 / 8 / 320 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| square | 160 / 8 / 320 | 4 / 2 / 1 | howell-rebuild | 0.000686 [0.000686, 0.000686] | 0.000838 | 3.6 | 67.5 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | timestamp-fast | 0.000287 [0.000287, 0.000287] | 0.000475 | 3.7 | 67.5 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | howell-segment | 0.001127 [0.001127, 0.001127] | 0.001284 | 3.7 | 67.5 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | closure-prototype | 0.000646 [0.000646, 0.000646] | 0.000911 | 3.8 | 67.5 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | timestamp-basic | 0.000660 [0.000660, 0.000660] | 0.000927 | 3.8 | 67.5 |
| square | 160 / 8 / 320 | 4 / 2 / 1 | howell-sparse | 0.000762 [0.000762, 0.000762] | 0.000842 | 4.0 | 67.5 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | howell-rebuild | 0.001096 [0.001096, 0.001096] | 0.001401 | 3.6 | 50.0 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | timestamp-fast | 0.000352 [0.000352, 0.000352] | 0.000481 | 3.7 | 50.0 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | howell-segment | 0.001254 [0.001254, 0.001254] | 0.001358 | 3.7 | 50.0 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | closure-prototype | 0.000628 [0.000628, 0.000628] | 0.000818 | 3.7 | 50.0 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | timestamp-basic | 0.000650 [0.000650, 0.000650] | 0.000791 | 3.8 | 50.0 |
| coupled-crt | 160 / 8 / 320 | 72 / 5 / 2 | howell-sparse | 0.001511 [0.001511, 0.001511] | 0.001596 | 4.1 | 50.0 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | xor-packed | unsupported | — | — | — |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | field-timestamp | 0.000615 [0.000615, 0.000615] | 0.000883 | 3.7 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | howell-rebuild | 0.001377 [0.001377, 0.001377] | 0.001606 | 3.6 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | howell-segment | 0.001627 [0.001627, 0.001627] | 0.001803 | 3.6 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | timestamp-fast | 0.000635 [0.000635, 0.000635] | 0.000880 | 3.7 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | closure-prototype | 0.000871 [0.000871, 0.000871] | 0.001174 | 3.7 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | timestamp-basic | 0.001016 [0.001016, 0.001016] | 0.001331 | 3.7 | 71.1 |
| word-boundary | 128 / 8 / 256 | 4294967291 / 1 / 1 | howell-sparse | 0.001694 [0.001694, 0.001694] | 0.001869 | 3.9 | 71.1 |

## Matched implementation comparison

| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |
| --- | --- | --- | --- |
| binary | 1.56x | 2.82x (xor-packed; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| square | 2.29x | 0.42x (howell-rebuild; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| coupled-crt | 1.85x | 0.32x (howell-rebuild; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| word-boundary | 1.60x | 1.03x (field-timestamp; <1 means timestamp-fast is faster) | short sample; use a larger workload |

## Reproduction

Run from the result directory:

```sh
python3 implementation/benchmark_cpp/run.py --profile smoke --tuning ubsan --repeats 1 --warmups 0 --seed 20260917 --timeout 15.0 --memory-mib 1024 --algorithms timestamp-basic,timestamp-fast,closure-prototype,howell-rebuild,howell-segment,howell-sparse,field-timestamp,xor-packed --quick-verification
```

Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.
Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.
Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.
Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.
A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.
