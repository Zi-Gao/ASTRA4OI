# C++ interval-membership benchmark

UTC: 2026-09-18T10:27:24.720882+00:00

All algorithms consume identical input files and emit identical ordered answers on completed runs.
Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.
This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.
RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.

- Host: Apple M3 Pro; Darwin 25.6.0
- Compiler: `Apple clang version 17.0.0 (clang-1700.6.3.2)`
- Flags: `-std=c++17 -Wall -Wextra -O3 -DNDEBUG -march=native`
- Profile: `standard`; seed 20260917; warmups=1; measured repeats=5
- Per-process wall timeout: 8.0 s; RSS budget: 512 MiB (sampled watchdog plus final high-water check)
- Correctness gate: 2,741,761 C++ membership assertions; exact arithmetic self-test passed.
- Howell candidates are local saturated-echelon implementations, not a tuned canonical-form library or a fast-matrix-multiplication implementation.
- closure-prototype is an internal historical ablation, not independent published prior art.
- No CPU pinning, frequency locking, or exclusive-machine guarantee; rerun on a quiet machine for publication.

[Raw measurements and dataset manifests](results.json)

## Results

Fast/basic is a matched speed ratio, not a comparison against the fastest competing method. A timeout is not an exact runtime.

| Case | n / d / q | m / K / w | Algorithm | Solve median [min, max] s | Program median s | Peak RSS MiB | YES % |
| --- | --- | --- | --- | --- | --- | --- | --- |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | timestamp-basic | 0.089139 [0.084245, 0.095944] | 0.106614 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-rebuild | 0.370996 [0.368880, 0.408312] | 0.385168 | 12.5 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-segment | 0.332310 [0.327675, 0.453671] | 0.346779 | 158.7 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-sparse | memory_limit | — | — | — |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | xor-packed | 0.005332 [0.004662, 0.006523] | 0.019195 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | closure-prototype | 0.087402 [0.079010, 0.094685] | 0.103280 | 13.3 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | field-timestamp | 0.037380 [0.035495, 0.039907] | 0.054228 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | timestamp-fast | 0.032791 [0.031739, 0.035235] | 0.044863 | 13.2 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | xor-packed | unsupported | — | — | — |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | field-timestamp | 0.031562 [0.031311, 0.033604] | 0.052508 | 6.5 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-rebuild | 0.171744 [0.171163, 0.171983] | 0.191996 | 6.2 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-segment | 0.169917 [0.168213, 0.176429] | 0.191071 | 41.3 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | timestamp-fast | 0.031780 [0.031257, 0.032545] | 0.052161 | 6.5 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | closure-prototype | 0.051194 [0.050001, 0.051511] | 0.071812 | 6.6 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | timestamp-basic | 0.053502 [0.051843, 0.054274] | 0.075087 | 6.6 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-sparse | 0.274167 [0.253916, 0.304963] | 0.294468 | 433.3 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-rebuild | 0.104567 [0.103649, 0.104743] | 0.111126 | 7.7 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | timestamp-fast | 0.032961 [0.026756, 0.034202] | 0.042538 | 8.3 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-segment | 0.137925 [0.133333, 0.146607] | 0.146218 | 80.0 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | closure-prototype | 0.083879 [0.083015, 0.088179] | 0.090559 | 8.4 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | timestamp-basic | 0.082126 [0.075149, 0.083750] | 0.091393 | 8.4 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | field-timestamp | unsupported | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | xor-packed | unsupported | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-rebuild | 0.115052 [0.114066, 0.123683] | 0.126598 | 6.0 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-fast | 0.163327 [0.162530, 0.166840] | 0.177597 | 6.5 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-segment | 0.139188 [0.137888, 0.145173] | 0.152133 | 37.4 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | closure-prototype | 0.709586 [0.705356, 0.745140] | 0.723373 | 6.6 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-basic | 0.610853 [0.525125, 0.632420] | 0.623795 | 6.6 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-sparse | 0.239787 [0.225653, 0.426580] | 0.252612 | 352.8 | 68.7 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | field-timestamp | unsupported | — | — | — |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | xor-packed | unsupported | — | — | — |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-rebuild | 0.154421 [0.153258, 0.157297] | 0.166802 | 6.0 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | timestamp-fast | 0.232071 [0.218383, 0.245094] | 0.244426 | 6.5 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-segment | 0.174308 [0.172603, 0.174614] | 0.188749 | 36.7 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | closure-prototype | 0.390294 [0.387045, 0.406824] | 0.403484 | 6.5 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | timestamp-basic | 0.351736 [0.331863, 0.454747] | 0.363601 | 6.6 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-sparse | 0.268950 [0.253859, 0.350426] | 0.282802 | 350.5 | 68.9 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | 0.372840 [0.370971, 0.397989] | 0.383117 | 7.2 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.062303 [0.061857, 0.074841] | 0.073073 | 7.5 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.399575 [0.393370, 0.460286] | 0.408893 | 46.8 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.174180 [0.171544, 0.206548] | 0.183636 | 7.6 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.167638 [0.164544, 0.188571] | 0.177449 | 7.6 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | memory_limit | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | field-timestamp | unsupported | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | xor-packed | unsupported | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-rebuild | 0.243836 [0.242482, 0.245892] | 0.259362 | 6.0 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | timestamp-fast | 0.081794 [0.081236, 0.088411] | 0.097929 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-segment | 0.285685 [0.284393, 0.391657] | 0.300805 | 38.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | closure-prototype | 0.178270 [0.174740, 0.187545] | 0.194070 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | timestamp-basic | 0.197898 [0.187971, 0.215087] | 0.213142 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-sparse | 0.376819 [0.359139, 0.417662] | 0.391676 | 355.3 | 68.8 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | xor-packed | unsupported | — | — | — |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | field-timestamp | 0.033100 [0.032477, 0.043128] | 0.056974 | 6.5 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-rebuild | 0.175267 [0.174498, 0.176507] | 0.197656 | 6.2 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-segment | 0.171311 [0.170641, 0.173412] | 0.194304 | 41.2 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | timestamp-fast | 0.034349 [0.032238, 0.035306] | 0.058109 | 6.5 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | closure-prototype | 0.053875 [0.050642, 0.054222] | 0.076469 | 6.6 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | timestamp-basic | 0.054297 [0.053016, 0.055432] | 0.076119 | 6.5 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-sparse | 0.275864 [0.251913, 0.280343] | 0.298417 | 433.3 | 69.5 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | field-timestamp | unsupported | — | — | — |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | xor-packed | unsupported | — | — | — |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-rebuild | 0.179903 [0.178538, 0.181849] | 0.203604 | 6.0 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | timestamp-fast | 0.065480 [0.065238, 0.066599] | 0.086071 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-segment | 0.206337 [0.204269, 0.219435] | 0.229747 | 37.1 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | closure-prototype | 0.134334 [0.129719, 0.279916] | 0.154448 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | timestamp-basic | 0.135805 [0.134096, 0.144056] | 0.155548 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-sparse | 0.288021 [0.281781, 0.308432] | 0.307627 | 351.6 | 69.3 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | timeout | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.058564 [0.057635, 0.060399] | 0.068315 | 7.6 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.628271 [0.626962, 0.632956] | 0.638746 | 46.7 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.166323 [0.165656, 0.167773] | 0.175883 | 7.6 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.151831 [0.150798, 0.152029] | 0.161162 | 7.6 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | memory_limit | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | field-timestamp | unsupported | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | xor-packed | unsupported | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-rebuild | 4.037387 [3.888781, 4.190467] | 4.048946 | 6.0 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-fast | 0.152208 [0.150317, 0.154472] | 0.166769 | 6.5 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-segment | 0.310069 [0.308039, 0.311472] | 0.323601 | 37.4 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | closure-prototype | 0.697106 [0.681728, 0.751741] | 0.710849 | 6.6 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-basic | 0.476391 [0.473394, 0.529058] | 0.488986 | 6.6 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-sparse | 0.575818 [0.569414, 0.600586] | 0.590764 | 352.8 | 50.0 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | field-timestamp | unsupported | — | — | — |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | xor-packed | unsupported | — | — | — |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-rebuild | 0.183403 [0.178227, 0.184668] | 0.199193 | 6.0 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | timestamp-fast | 0.011090 [0.010757, 0.011654] | 0.028348 | 6.5 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-segment | 0.128168 [0.125528, 0.164877] | 0.147642 | 35.8 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | closure-prototype | 0.030669 [0.029304, 0.035682] | 0.047375 | 6.7 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | timestamp-basic | 0.037981 [0.036264, 0.046224] | 0.055952 | 6.7 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-sparse | 0.261223 [0.234660, 0.294564] | 0.280993 | 348.0 | 60.8 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | 0.332345 [0.329376, 0.380542] | 0.343309 | 7.2 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.022177 [0.021149, 0.023821] | 0.031957 | 7.6 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.238281 [0.236447, 0.239808] | 0.247808 | 39.0 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.058311 [0.054002, 0.059393] | 0.068938 | 7.6 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.054221 [0.053093, 0.056256] | 0.064683 | 7.6 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | 0.471802 [0.448524, 0.509716] | 0.482803 | 455.0 | 61.5 |

## Matched implementation comparison

| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |
| --- | --- | --- | --- |
| binary-d64 | 2.72x | 6.15x (xor-packed; <1 means timestamp-fast is faster) | — |
| prime-d32 | 1.68x | 1.01x (field-timestamp; <1 means timestamp-fast is faster) | — |
| square-d32 | 2.49x | 0.32x (howell-rebuild; <1 means timestamp-fast is faster) | fast timing CV > 10% |
| deep-power-d24 | 3.74x | 1.42x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| odd-power-d24 | 1.52x | 1.50x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| crt-d32 | 2.69x | 0.17x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| many-primes-d24 | 2.42x | 0.34x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| word-boundary-d32 | 1.58x | 1.04x (field-timestamp; <1 means timestamp-fast is faster) | — |
| composite-boundary-d24 | 2.07x | 0.36x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| coupled-crt-d32 | 2.59x | 0.09x (howell-segment; <1 means timestamp-fast is faster) | — |
| nonunit-power-d24 | 3.13x | 0.49x (howell-segment; <1 means timestamp-fast is faster) | — |
| valuation-ladder-d24 | 3.42x | 0.09x (howell-segment; <1 means timestamp-fast is faster) | — |
| zeros-duplicates-d32 | 2.44x | 0.09x (howell-segment; <1 means timestamp-fast is faster) | — |

## Reproduction

Run from the result directory:

```sh
python3 implementation/benchmark_cpp/run.py --profile standard --tuning native --repeats 5 --warmups 1 --seed 20260917 --timeout 8.0 --memory-mib 512 --algorithms timestamp-basic,timestamp-fast,closure-prototype,howell-rebuild,howell-segment,howell-sparse,field-timestamp,xor-packed
```

Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.
Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.
Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.
Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.
A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.
