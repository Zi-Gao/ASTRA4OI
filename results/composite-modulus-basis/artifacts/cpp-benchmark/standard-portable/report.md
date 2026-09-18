# C++ interval-membership benchmark

UTC: 2026-09-18T15:17:26.624196+00:00

All algorithms consume identical input files and emit identical ordered answers on completed runs.
Primary time is the full solve (construction, offline bucketing, queries, allocation and destruction), excluding parsing/output.
This is a static batch workload: offline reordering is allowed. It does not benchmark online historical snapshots.
RSS is whole-process high-water memory, including input and output arrays. One compiler configuration is shared by every algorithm.

- Host: Apple M3 Pro; Darwin 25.6.0
- Compiler: `Apple clang version 17.0.0 (clang-1700.6.3.2)`
- Flags: `-std=c++17 -Wall -Wextra -O2 -DNDEBUG`
- Profile: `standard`; seed 20260917; warmups=1; measured repeats=3
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
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | timestamp-basic | 0.090868 [0.084789, 0.092341] | 0.106962 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-rebuild | 0.367891 [0.367462, 0.511683] | 0.382247 | 12.5 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-segment | 0.331543 [0.329330, 0.391990] | 0.343282 | 158.7 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | howell-sparse | memory_limit | — | — | — |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | xor-packed | 0.005631 [0.005392, 0.006162] | 0.020303 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | closure-prototype | 0.083753 [0.080618, 0.086570] | 0.098681 | 13.3 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | field-timestamp | 0.036831 [0.032769, 0.037553] | 0.054013 | 13.2 | 69.0 |
| binary-d64 | 20000 / 64 / 20000 | 2 / 1 / 1 | timestamp-fast | 0.036506 [0.034018, 0.038691] | 0.048761 | 13.2 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | xor-packed | unsupported | — | — | — |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | field-timestamp | 0.031518 [0.031513, 0.032515] | 0.052680 | 6.6 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-rebuild | 0.173901 [0.172728, 0.318694] | 0.196448 | 6.2 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-segment | 0.169111 [0.169050, 0.174106] | 0.190819 | 41.2 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | timestamp-fast | 0.032872 [0.032008, 0.033712] | 0.054953 | 6.5 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | closure-prototype | 0.052117 [0.050702, 0.053559] | 0.072199 | 6.6 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | timestamp-basic | 0.053454 [0.052095, 0.056950] | 0.075629 | 6.6 | 69.0 |
| prime-d32 | 10000 / 32 / 20000 | 998244353 / 1 / 1 | howell-sparse | 0.257553 [0.254370, 0.261305] | 0.279561 | 433.3 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | field-timestamp | unsupported | — | — | — |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | xor-packed | unsupported | — | — | — |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-rebuild | 0.104559 [0.104391, 0.105174] | 0.111289 | 7.7 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | timestamp-fast | 0.035109 [0.029835, 0.036030] | 0.044851 | 8.3 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-segment | 0.140098 [0.139998, 0.141865] | 0.149264 | 80.0 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | closure-prototype | 0.085696 [0.084782, 0.090429] | 0.092523 | 8.4 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | timestamp-basic | 0.081760 [0.076084, 0.083271] | 0.090371 | 8.4 | 69.0 |
| square-d32 | 20000 / 32 / 20000 | 4 / 2 / 1 | howell-sparse | memory_limit | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | field-timestamp | unsupported | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | xor-packed | unsupported | — | — | — |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-rebuild | 0.115208 [0.114489, 0.115285] | 0.126544 | 6.0 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-fast | 0.176311 [0.175720, 0.176362] | 0.191983 | 6.5 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-segment | 0.137273 [0.136991, 0.283565] | 0.149347 | 37.5 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | closure-prototype | 0.747423 [0.719324, 0.749397] | 0.759510 | 6.6 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-basic | 0.543520 [0.538381, 0.601404] | 0.556290 | 6.6 | 68.7 |
| deep-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-sparse | 0.224100 [0.218902, 0.224185] | 0.236998 | 352.8 | 68.7 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | field-timestamp | unsupported | — | — | — |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | xor-packed | unsupported | — | — | — |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-rebuild | 0.155434 [0.153541, 0.156878] | 0.170319 | 6.0 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | timestamp-fast | 0.238230 [0.228231, 0.238666] | 0.251950 | 6.5 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-segment | 0.173919 [0.173348, 0.174523] | 0.188449 | 36.8 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | closure-prototype | 0.429419 [0.394657, 0.549538] | 0.445154 | 6.6 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | timestamp-basic | 0.335642 [0.334905, 0.353586] | 0.348388 | 6.6 | 68.9 |
| odd-power-d24 | 12000 / 24 / 24000 | 59049 / 10 / 1 | howell-sparse | 0.265583 [0.253422, 0.266194] | 0.278971 | 350.5 | 68.9 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | 0.372544 [0.369013, 0.426520] | 0.381685 | 7.2 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.066577 [0.066242, 0.068442] | 0.075384 | 7.5 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.395272 [0.392844, 0.540204] | 0.406315 | 46.8 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.178638 [0.174946, 0.178873] | 0.189434 | 7.6 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.167371 [0.160147, 0.169691] | 0.177378 | 7.6 | 68.3 |
| crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | memory_limit | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | field-timestamp | unsupported | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | xor-packed | unsupported | — | — | — |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-rebuild | 0.240651 [0.240624, 0.290700] | 0.255583 | 6.0 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | timestamp-fast | 0.088313 [0.087030, 0.089021] | 0.106929 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-segment | 0.284023 [0.282321, 0.291106] | 0.297969 | 38.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | closure-prototype | 0.186099 [0.177827, 0.187020] | 0.200587 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | timestamp-basic | 0.190959 [0.189367, 0.197578] | 0.207535 | 6.5 | 68.8 |
| many-primes-d24 | 12000 / 24 / 24000 | 9699690 / 8 / 8 | howell-sparse | 0.347004 [0.344206, 0.351281] | 0.362253 | 355.4 | 68.8 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | xor-packed | unsupported | — | — | — |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | field-timestamp | 0.032635 [0.032337, 0.035564] | 0.056799 | 6.5 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-rebuild | 0.175032 [0.174879, 0.177148] | 0.197858 | 6.2 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-segment | 0.171307 [0.171116, 0.172119] | 0.194199 | 41.3 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | timestamp-fast | 0.033515 [0.033234, 0.033568] | 0.056435 | 6.5 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | closure-prototype | 0.052646 [0.052006, 0.053478] | 0.075010 | 6.6 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | timestamp-basic | 0.053885 [0.053417, 0.054824] | 0.078214 | 6.6 | 69.5 |
| word-boundary-d32 | 10000 / 32 / 20000 | 4294967291 / 1 / 1 | howell-sparse | 0.257849 [0.256287, 0.296179] | 0.282530 | 433.3 | 69.5 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | field-timestamp | unsupported | — | — | — |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | xor-packed | unsupported | — | — | — |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-rebuild | 0.181608 [0.179709, 0.190053] | 0.208201 | 6.0 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | timestamp-fast | 0.069251 [0.069010, 0.070288] | 0.089029 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-segment | 0.205807 [0.204795, 0.207043] | 0.228059 | 37.1 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | closure-prototype | 0.137981 [0.134175, 0.140638] | 0.157564 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | timestamp-basic | 0.140977 [0.139308, 0.289839] | 0.168010 | 6.5 | 69.3 |
| composite-boundary-d24 | 12000 / 24 / 24000 | 4294967295 / 5 / 5 | howell-sparse | 0.282361 [0.281814, 0.287791] | 0.303553 | 351.6 | 69.3 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | timeout | — | — | — |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.065266 [0.063330, 0.066170] | 0.074566 | 7.5 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.712976 [0.630604, 0.782595] | 0.724271 | 46.7 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.172700 [0.168514, 0.178524] | 0.182120 | 7.6 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.164196 [0.156429, 0.164816] | 0.173650 | 7.6 | 50.0 |
| coupled-crt-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | memory_limit | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | field-timestamp | unsupported | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | xor-packed | unsupported | — | — | — |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-rebuild | 4.068172 [3.864743, 4.077070] | 4.080388 | 6.0 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-fast | 0.163499 [0.162877, 0.165272] | 0.179712 | 6.5 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-segment | 0.307080 [0.304196, 0.310979] | 0.319043 | 37.5 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | closure-prototype | 0.706567 [0.688659, 0.729278] | 0.718599 | 6.6 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | timestamp-basic | 0.554626 [0.497948, 0.622385] | 0.566500 | 6.6 | 50.0 |
| nonunit-power-d24 | 12000 / 24 / 24000 | 65536 / 16 / 1 | howell-sparse | 0.557606 [0.544561, 0.599175] | 0.572600 | 352.8 | 50.0 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | field-timestamp | unsupported | — | — | — |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | xor-packed | unsupported | — | — | — |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-rebuild | 0.184792 [0.184491, 0.186980] | 0.201724 | 6.0 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | timestamp-fast | 0.012577 [0.012230, 0.013034] | 0.030810 | 6.5 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-segment | 0.128350 [0.124565, 0.129733] | 0.147420 | 35.8 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | closure-prototype | 0.030141 [0.028499, 0.033014] | 0.046679 | 6.7 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | timestamp-basic | 0.038398 [0.038173, 0.038916] | 0.056842 | 6.6 | 60.8 |
| valuation-ladder-d24 | 12000 / 24 / 24000 | 1073741824 / 30 / 1 | howell-sparse | 0.240982 [0.237191, 0.242022] | 0.258488 | 348.0 | 60.8 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | field-timestamp | unsupported | — | — | — |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | xor-packed | unsupported | — | — | — |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-rebuild | 0.327060 [0.326652, 0.469075] | 0.337747 | 7.2 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-fast | 0.024436 [0.023672, 0.025903] | 0.034781 | 7.5 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-segment | 0.239914 [0.239257, 0.243178] | 0.249380 | 39.0 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | closure-prototype | 0.054732 [0.054697, 0.057058] | 0.064585 | 7.6 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | timestamp-basic | 0.054717 [0.054388, 0.055358] | 0.065286 | 7.6 | 61.5 |
| zeros-duplicates-d32 | 12000 / 32 / 24000 | 72 / 5 / 2 | howell-sparse | 0.507307 [0.442387, 0.514238] | 0.519478 | 455.1 | 61.5 |

## Matched implementation comparison

| Case | Basic / fast solve ratio | Fast / best completed non-timestamp baseline solve ratio | Notes |
| --- | --- | --- | --- |
| binary-d64 | 2.49x | 6.48x (xor-packed; <1 means timestamp-fast is faster) | — |
| prime-d32 | 1.63x | 1.04x (field-timestamp; <1 means timestamp-fast is faster) | — |
| square-d32 | 2.33x | 0.34x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| deep-power-d24 | 3.08x | 1.53x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| odd-power-d24 | 1.41x | 1.53x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| crt-d32 | 2.51x | 0.18x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| many-primes-d24 | 2.16x | 0.37x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| word-boundary-d32 | 1.61x | 1.03x (field-timestamp; <1 means timestamp-fast is faster) | — |
| composite-boundary-d24 | 2.04x | 0.38x (howell-rebuild; <1 means timestamp-fast is faster) | — |
| coupled-crt-d32 | 2.52x | 0.09x (howell-segment; <1 means timestamp-fast is faster) | — |
| nonunit-power-d24 | 3.39x | 0.53x (howell-segment; <1 means timestamp-fast is faster) | — |
| valuation-ladder-d24 | 3.05x | 0.10x (howell-segment; <1 means timestamp-fast is faster) | — |
| zeros-duplicates-d32 | 2.24x | 0.10x (howell-segment; <1 means timestamp-fast is faster) | — |

## Reproduction

Run from the result directory:

```sh
python3 implementation/benchmark_cpp/run.py --profile standard --tuning portable --repeats 3 --warmups 1 --seed 20260917 --timeout 8.0 --memory-mib 512 --algorithms timestamp-basic,timestamp-fast,closure-prototype,howell-rebuild,howell-segment,howell-sparse,field-timestamp,xor-packed
```

Dataset SHA-256, distributions, interval-length histograms, oracle probes, compiler/source fingerprints, shuffled run order, every raw repetition and failures are in results.json.
Every odd-indexed target is a known linear combination; coupled/nonunit distributions additionally force every even-indexed target outside the full generated module.
Eight fixed short-interval probes per performance dataset use the independent integer-lattice oracle; complete outputs are cross-compared across algorithms.
Warmups are excluded. Algorithms run serially, in a deterministic shuffled order each round; after a timeout/memory failure, further repeats of that candidate are not attempted.
A failed or incomplete candidate receives no speedup number. Unsupported field-only methods are reported rather than used on composite moduli.
