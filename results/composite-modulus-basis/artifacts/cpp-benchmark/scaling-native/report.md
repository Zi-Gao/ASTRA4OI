# C++ interval-membership benchmark

UTC: 2026-09-18T15:19:43.581336+00:00

All algorithms consume identical input files and emit identical ordered answers on completed runs.
Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.
This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.
RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.

- Host: Apple M3 Pro; Darwin 25.6.0
- Compiler: `Apple clang version 17.0.0 (clang-1700.6.3.2)`
- Flags: `-std=c++17 -Wall -Wextra -O3 -DNDEBUG -march=native`
- Profile: `scaling`; seed 20260917; warmups=1; measured repeats=3
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
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.018460 [0.017306, 0.019529] | 0.021295 | 3.0 | 70.4 |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.004158 [0.004103, 0.004456] | 0.006308 | 3.3 | 70.4 |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | howell-segment | 0.028251 [0.026778, 0.028768] | 0.031566 | 8.5 | 70.4 |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | closure-prototype | 0.013900 [0.012817, 0.014604] | 0.016915 | 3.4 | 70.4 |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.013003 [0.012712, 0.013734] | 0.016052 | 3.4 | 70.4 |
| dimension-8 | 8000 / 8 / 16000 | 4 / 2 / 1 | howell-sparse | 0.052074 [0.045132, 0.121456] | 0.055387 | 46.4 | 70.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.034602 [0.031144, 0.034699] | 0.038811 | 3.8 | 69.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.005743 [0.005733, 0.005945] | 0.008168 | 4.0 | 69.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | howell-segment | 0.044245 [0.041353, 0.044697] | 0.048351 | 14.3 | 69.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | closure-prototype | 0.020605 [0.020399, 0.021479] | 0.024173 | 4.1 | 69.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.019868 [0.015684, 0.020265] | 0.023156 | 4.1 | 69.4 |
| dimension-16 | 8000 / 16 / 16000 | 4 / 2 / 1 | howell-sparse | 0.078752 [0.077071, 0.081008] | 0.082559 | 116.6 | 69.4 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.086378 [0.083120, 0.086769] | 0.091010 | 5.2 | 69.1 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.013024 [0.012682, 0.013808] | 0.017355 | 5.5 | 69.1 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | howell-segment | 0.092872 [0.088639, 0.093719] | 0.098672 | 26.2 | 69.1 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | closure-prototype | 0.041124 [0.037871, 0.045515] | 0.046251 | 5.6 | 69.1 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.037568 [0.035474, 0.044177] | 0.041820 | 5.6 | 69.1 |
| dimension-32 | 8000 / 32 / 16000 | 4 / 2 / 1 | howell-sparse | 0.180468 [0.169159, 0.191266] | 0.186622 | 334.9 | 69.1 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.438767 [0.437514, 0.442439] | 0.448581 | 8.2 | 68.5 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.037347 [0.036190, 0.041263] | 0.044786 | 8.5 | 68.5 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | howell-segment | 0.357646 [0.352017, 0.358854] | 0.366244 | 52.4 | 68.5 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | closure-prototype | 0.116511 [0.108914, 0.117640] | 0.126424 | 8.5 | 68.5 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.101771 [0.101193, 0.104205] | 0.110825 | 8.5 | 68.5 |
| dimension-64 | 8000 / 64 / 16000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | timestamp-basic | 0.017220 [0.013437, 0.018067] | 0.023608 | 4.9 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | howell-rebuild | 0.044574 [0.043229, 0.048022] | 0.050563 | 4.5 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | howell-segment | 0.049894 [0.044045, 0.054491] | 0.056279 | 20.6 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | howell-sparse | 0.103186 [0.102314, 0.108632] | 0.107447 | 217.4 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | xor-packed | 0.002162 [0.002143, 0.002216] | 0.006741 | 4.8 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | closure-prototype | 0.012956 [0.009048, 0.017860] | 0.016420 | 4.9 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | field-timestamp | 0.008022 [0.005808, 0.008762] | 0.014661 | 4.8 | 69.0 |
| exponent-1 | 8000 / 24 / 16000 | 2 / 1 / 1 | timestamp-fast | 0.005624 [0.004394, 0.008284] | 0.009612 | 4.8 | 69.0 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.053365 [0.049028, 0.053996] | 0.057867 | 4.5 | 68.5 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.012045 [0.011611, 0.012083] | 0.016668 | 4.8 | 68.5 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | howell-segment | 0.064995 [0.064071, 0.067600] | 0.069830 | 21.3 | 68.5 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | closure-prototype | 0.030813 [0.027389, 0.034440] | 0.035605 | 4.9 | 68.5 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.025434 [0.025031, 0.028137] | 0.028998 | 4.8 | 68.5 |
| exponent-2 | 8000 / 24 / 16000 | 4 / 2 / 1 | howell-sparse | 0.119450 [0.114658, 0.135777] | 0.123902 | 219.5 | 68.5 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | field-timestamp | unsupported | — | — | — |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | xor-packed | unsupported | — | — | — |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | howell-rebuild | 0.066728 [0.066050, 0.067700] | 0.072411 | 4.6 | 68.3 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | timestamp-fast | 0.023566 [0.022854, 0.023823] | 0.030641 | 4.8 | 68.3 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | howell-segment | 0.078386 [0.078268, 0.082259] | 0.084009 | 21.7 | 68.3 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | closure-prototype | 0.068531 [0.067711, 0.073987] | 0.074208 | 4.9 | 68.3 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | timestamp-basic | 0.060572 [0.059448, 0.062202] | 0.065862 | 4.9 | 68.3 |
| exponent-4 | 8000 / 24 / 16000 | 16 / 4 / 1 | howell-sparse | 0.130666 [0.130591, 0.159823] | 0.136152 | 220.4 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | field-timestamp | unsupported | — | — | — |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | xor-packed | unsupported | — | — | — |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | howell-rebuild | 0.078088 [0.078063, 0.078229] | 0.085899 | 4.6 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | timestamp-fast | 0.049108 [0.048098, 0.049695] | 0.056941 | 4.8 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | howell-segment | 0.087009 [0.085751, 0.087973] | 0.094528 | 21.7 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | closure-prototype | 0.180282 [0.179464, 0.184765] | 0.187787 | 4.9 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | timestamp-basic | 0.152826 [0.146399, 0.158608] | 0.159206 | 4.9 | 68.3 |
| exponent-8 | 8000 / 24 / 16000 | 256 / 8 / 1 | howell-sparse | 0.143432 [0.140038, 0.145080] | 0.150999 | 220.6 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | field-timestamp | unsupported | — | — | — |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | xor-packed | unsupported | — | — | — |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | howell-rebuild | 0.077019 [0.076856, 0.082036] | 0.085491 | 4.6 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | timestamp-fast | 0.111525 [0.110784, 0.111567] | 0.121112 | 4.9 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | howell-segment | 0.092618 [0.088219, 0.093537] | 0.104375 | 21.7 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | closure-prototype | 0.504675 [0.476692, 0.638128] | 0.515462 | 4.9 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | timestamp-basic | 0.345202 [0.339313, 0.400674] | 0.354796 | 4.9 | 68.3 |
| exponent-16 | 8000 / 24 / 16000 | 65536 / 16 / 1 | howell-sparse | 0.149743 [0.149160, 0.151348] | 0.159512 | 220.7 | 68.3 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | field-timestamp | unsupported | — | — | — |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | xor-packed | unsupported | — | — | — |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | howell-rebuild | 0.079616 [0.079179, 0.079661] | 0.091885 | 4.6 | 68.2 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | timestamp-fast | 0.228587 [0.227749, 0.377297] | 0.243379 | 4.9 | 68.2 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | howell-segment | 0.090127 [0.089375, 0.092414] | 0.103858 | 21.7 | 68.2 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | closure-prototype | 1.274614 [1.232069, 1.286495] | 1.287207 | 5.0 | 68.2 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | timestamp-basic | 0.742743 [0.740720, 0.747345] | 0.760845 | 5.0 | 68.2 |
| exponent-30 | 8000 / 24 / 16000 | 1073741824 / 30 / 1 | howell-sparse | 0.146195 [0.143137, 0.148632] | 0.158213 | 220.6 | 68.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | howell-rebuild | 0.008393 [0.008233, 0.009245] | 0.010745 | 2.9 | 70.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | timestamp-fast | 0.011304 [0.011138, 0.011467] | 0.013020 | 3.0 | 70.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | howell-segment | 0.021121 [0.020852, 0.025424] | 0.023017 | 23.8 | 70.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | closure-prototype | 0.039098 [0.037826, 0.047276] | 0.041176 | 3.0 | 70.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | timestamp-basic | 0.038506 [0.032000, 0.040497] | 0.040859 | 3.0 | 70.2 |
| queries-1000 | 8000 / 32 / 1000 | 4 / 2 / 1 | howell-sparse | 0.157475 [0.149287, 0.158387] | 0.160160 | 332.5 | 70.2 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | howell-rebuild | 0.045806 [0.043080, 0.046962] | 0.048472 | 4.0 | 69.0 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | timestamp-fast | 0.012422 [0.011441, 0.012532] | 0.015639 | 4.2 | 69.0 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | howell-segment | 0.055528 [0.054924, 0.058565] | 0.059236 | 24.9 | 69.0 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | closure-prototype | 0.039944 [0.037083, 0.043165] | 0.043568 | 4.2 | 69.0 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | timestamp-basic | 0.037278 [0.034948, 0.037453] | 0.040801 | 4.2 | 69.0 |
| queries-8000 | 8000 / 32 / 8000 | 4 / 2 / 1 | howell-sparse | 0.161373 [0.159881, 0.170578] | 0.164663 | 333.6 | 69.0 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | howell-rebuild | 0.336754 [0.328187, 0.351918] | 0.349052 | 12.8 | 68.8 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | timestamp-fast | 0.024827 [0.023988, 0.026340] | 0.037465 | 13.4 | 68.8 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | howell-segment | 0.321546 [0.314935, 0.335145] | 0.335741 | 33.7 | 68.8 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | closure-prototype | 0.059702 [0.058313, 0.060194] | 0.073317 | 13.5 | 68.8 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | timestamp-basic | 0.061990 [0.056881, 0.065763] | 0.075077 | 13.5 | 68.8 |
| queries-64000 | 8000 / 32 / 64000 | 4 / 2 / 1 | howell-sparse | 0.274009 [0.264105, 0.286137] | 0.288631 | 342.5 | 68.8 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.085310 [0.079012, 0.086626] | 0.089619 | 4.2 | 67.2 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.005422 [0.005038, 0.005973] | 0.009409 | 4.4 | 67.2 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | howell-segment | 0.083257 [0.082188, 0.084734] | 0.088970 | 6.8 | 67.2 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | closure-prototype | 0.014242 [0.009815, 0.014803] | 0.019058 | 4.4 | 67.2 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.010466 [0.010337, 0.012526] | 0.013450 | 4.5 | 67.2 |
| length-1000 | 1000 / 32 / 16000 | 4 / 2 / 1 | howell-sparse | 0.051323 [0.041491, 0.052975] | 0.056051 | 31.4 | 67.2 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | howell-rebuild | 0.087173 [0.085731, 0.088527] | 0.100950 | 13.4 | 69.5 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | timestamp-fast | 0.075227 [0.074875, 0.078162] | 0.087305 | 15.0 | 69.5 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | howell-segment | 0.190680 [0.187919, 0.190853] | 0.202770 | 181.2 | 69.5 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | closure-prototype | 0.266745 [0.260804, 0.280341] | 0.278951 | 15.1 | 69.5 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | timestamp-basic | 0.229827 [0.227525, 0.286767] | 0.244064 | 15.1 | 69.5 |
| length-64000 | 64000 / 32 / 16000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | field-timestamp | unsupported | — | — | — |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | xor-packed | unsupported | — | — | — |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | howell-rebuild | 0.102287 [0.094545, 0.102718] | 0.107121 | 4.5 | 69.1 |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | timestamp-fast | 0.010860 [0.010737, 0.011156] | 0.014579 | 4.8 | 69.1 |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | howell-segment | 0.116505 [0.115714, 0.117310] | 0.121505 | 21.7 | 69.1 |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | closure-prototype | 0.026031 [0.020630, 0.028683] | 0.030588 | 4.9 | 69.1 |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | timestamp-basic | 0.024460 [0.022041, 0.027606] | 0.028166 | 4.9 | 69.1 |
| components-2 | 8000 / 24 / 16000 | 6 / 2 / 2 | howell-sparse | 0.164929 [0.158264, 0.165740] | 0.169395 | 220.7 | 69.1 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | field-timestamp | unsupported | — | — | — |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | xor-packed | unsupported | — | — | — |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | howell-rebuild | 0.147053 [0.145094, 0.147910] | 0.154172 | 4.6 | 68.6 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | timestamp-fast | 0.022563 [0.022557, 0.027392] | 0.028991 | 4.8 | 68.6 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | howell-segment | 0.168497 [0.168121, 0.170027] | 0.175861 | 22.2 | 68.6 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | closure-prototype | 0.052504 [0.049788, 0.053753] | 0.060694 | 4.9 | 68.6 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | timestamp-basic | 0.055298 [0.053298, 0.058539] | 0.062697 | 4.8 | 68.6 |
| components-4 | 8000 / 24 / 16000 | 210 / 4 / 4 | howell-sparse | 0.212079 [0.210102, 0.215919] | 0.220317 | 222.0 | 68.6 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | field-timestamp | unsupported | — | — | — |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | xor-packed | unsupported | — | — | — |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | howell-rebuild | 0.165274 [0.161767, 0.166307] | 0.178511 | 4.6 | 68.7 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | timestamp-fast | 0.056263 [0.054868, 0.057561] | 0.068565 | 4.8 | 68.7 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | howell-segment | 0.191366 [0.187104, 0.191785] | 0.204612 | 22.4 | 68.7 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | closure-prototype | 0.121144 [0.115754, 0.123299] | 0.132273 | 4.9 | 68.7 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | timestamp-basic | 0.125295 [0.124522, 0.130332] | 0.134765 | 4.9 | 68.7 |
| components-8 | 8000 / 24 / 16000 | 9699690 / 8 / 8 | howell-sparse | 0.229380 [0.225950, 0.232480] | 0.240354 | 222.3 | 68.7 |

## Matched implementation comparison

| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |
| --- | --- | --- | --- |
| dimension-8 | 3.13x | 0.23x (howell-rebuild; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| dimension-16 | 3.46x | 0.17x (howell-rebuild; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| dimension-32 | 2.88x | 0.15x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| dimension-64 | 2.72x | 0.10x (howell-segment; <1 means timestamp-fast is faster) | — |
| exponent-1 | 3.06x | 2.60x (xor-packed; <1 means timestamp-fast is faster) | fast timing CV > 10%; short sample; use a larger workload |
| exponent-2 | 2.11x | 0.23x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| exponent-4 | 2.57x | 0.35x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| exponent-8 | 3.11x | 0.63x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| exponent-16 | 3.10x | 1.45x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| exponent-30 | 3.25x | 2.87x (howell-rebuild; <1 means timestamp-fast is faster) | fast timing CV > 10% |
| queries-1000 | 3.41x | 1.35x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| queries-8000 | 3.00x | 0.27x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| queries-64000 | 2.50x | 0.09x (howell-sparse; <1 means timestamp-fast is faster) | — |
| length-1000 | 1.93x | 0.11x (howell-sparse; <1 means timestamp-fast is faster) | short sample; use a larger workload |
| length-64000 | 3.06x | 0.86x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| components-2 | 2.25x | 0.11x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| components-4 | 2.45x | 0.15x (howell-rebuild; <1 means timestamp-fast is faster) | fast timing CV > 10% |
| components-8 | 2.23x | 0.34x (howell-rebuild; <1 means timestamp-fast is faster) | — |

## Reproduction

Run from the result directory:

```sh
python3 implementation/benchmark_cpp/run.py --profile scaling --tuning native --repeats 3 --warmups 1 --seed 20260917 --timeout 8.0 --memory-mib 512 --algorithms timestamp-basic,timestamp-fast,closure-prototype,howell-rebuild,howell-segment,howell-sparse,field-timestamp,xor-packed
```

Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.
Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.
Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.
Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.
A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.
