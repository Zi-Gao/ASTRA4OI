"""Fixed-seed performance samples with independent integer-lattice spot checks.

From the artifact root, run `python3 implementation/benchmark.py > artifacts/benchmarks.txt` to refresh the saved report.
Timings are observations on the current machine, not worst-case guarantees.
"""

import argparse
import math
import platform
import random
import sys
import time

from solver import PrimePowerBasis, solve_offline
from tests.oracles import LatticeOracle


CASES = {
    "small": ((2, 3), (3, 2)),
    "large-prime-power": ((1000000007, 2),),
    "large-crt": ((998244353, 2), (1000000007, 2)),
}


def run_case(name, factors, n, dimension, query_count):
    rng = random.Random(120926)
    modulus = math.prod(p**k for p, k in factors)
    vectors = [tuple(rng.randrange(modulus) for _ in range(dimension)) for _ in range(n)]
    queries = []
    for index in range(query_count):
        right = rng.randrange(1, n + 1)
        left = rng.randrange(max(1, right - 2 * dimension), right + 1)
        if index % 2:
            interval = vectors[left - 1:right]
            coefficients = [rng.randrange(modulus) for _ in interval]
            target = tuple(
                sum(c * row[j] for c, row in zip(coefficients, interval)) % modulus
                for j in range(dimension)
            )
        else:
            target = tuple(rng.randrange(modulus) for _ in range(dimension))
        queries.append((left, right, target))
    started = time.perf_counter()
    answers = solve_offline(vectors, modulus, queries, factors=factors)
    elapsed = time.perf_counter() - started
    print(f"Case: {name}; seed=120926; factors={factors}", flush=True)
    print(f"n={n}, d={dimension}, q={query_count}, modulus_bits={modulus.bit_length()}", flush=True)
    print(f"Offline solve only: {elapsed:.3f} seconds; YES={sum(answers)}, NO={len(answers) - sum(answers)}", flush=True)
    samples = 0
    for index in range(0, query_count, 97):
        left, right, target = queries[index]
        oracle = LatticeOracle(vectors[left - 1:right], modulus, dimension)
        assert answers[index] == oracle.contains(target), (name, index)
        samples += 1
    print(f"PASS {samples} sampled answers against independent integer-lattice oracle", flush=True)
    for p, k in factors:
        basis = PrimePowerBasis(p, k, dimension)
        for vector in vectors:
            old = basis.row_reductions, basis.slot_writes, basis.heap_pops, basis.column_visits, basis.initial_row_passes
            basis.append(vector)
            reductions, writes, pops, visits, initial = (
                value - prior for value, prior in zip(
                    (basis.row_reductions, basis.slot_writes, basis.heap_pops, basis.column_visits, basis.initial_row_passes), old
                )
            )
            assert visits <= k * dimension
            assert reductions <= visits and writes <= visits
            assert pops <= k * (dimension + 1) and basis.max_pending <= k
            assert (initial + reductions + writes) * dimension <= 3 * k * dimension**2
        print(f"PASS p={p}, k={k}: reductions={basis.row_reductions}, writes={basis.slot_writes}, pops={basis.heap_pops}, max_pending={basis.max_pending}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=(*CASES, "all"), default="all")
    parser.add_argument("--n", type=int, default=4000)
    parser.add_argument("--dimension", type=int, default=16)
    parser.add_argument("--queries", type=int, default=8000)
    args = parser.parse_args()
    if not __debug__:
        parser.error("verification requires assertions; do not use python -O")
    if min(args.n, args.dimension) < 1 or args.queries < 0:
        parser.error("n and dimension must be positive; queries must be nonnegative")
    print(f"Python {sys.version.split()[0]}; {platform.system()} {platform.machine()}", flush=True)
    for name, factors in CASES.items():
        if args.case in (name, "all"):
            run_case(name, factors, args.n, args.dimension, args.queries)


if __name__ == "__main__":
    main()
