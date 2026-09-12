"""Reproduce the fixed-seed performance example; outputs are saved locally."""

from pathlib import Path
import random
import time

from solver import PrimePowerBasis, solve_offline
from experiment import PrimePowerBasis as ClosureBasis


def main():
    rng = random.Random(120926)
    n, dimension, query_count, modulus = 4000, 16, 8000, 72
    vectors = [tuple(rng.randrange(modulus) for _ in range(dimension)) for _ in range(n)]
    queries = []
    for _ in range(query_count):
        right = rng.randrange(1, n + 1)
        left = rng.randrange(max(1, right - 2 * dimension), right + 1)
        target = tuple(rng.randrange(modulus) for _ in range(dimension))
        queries.append((left, right, target))
    started = time.perf_counter()
    answers = solve_offline(vectors, modulus, queries, factors=[(2, 3), (3, 2)])
    elapsed = time.perf_counter() - started
    lines = [
        "Seed: 120926",
        f"n={n}, d={dimension}, q={query_count}, m={modulus}=2^3*3^2",
        f"Offline total: {elapsed:.3f} seconds",
        f"YES count: {sum(answers)}",
    ]
    samples = 0
    for index in range(0, query_count, 97):
        left, right, target = queries[index]
        expected = True
        for p, k in [(2, 3), (3, 2)]:
            check = ClosureBasis(p, k, dimension)
            for timestamp, row in enumerate(vectors[left - 1:right], 1):
                check.insert(tuple(a % (p**k) for a in row), timestamp)
            expected = expected and check.contains(target)
        assert answers[index] == expected
        samples += 1
    lines.append(f"{samples} sampled answers agree with fresh explicit-closure bases.")
    for p, k in [(2, 3), (3, 2)]:
        basis = PrimePowerBasis(p, k, dimension)
        for vector in vectors:
            reductions, writes = basis.row_reductions, basis.slot_writes
            basis.append(vector)
            assert basis.row_reductions - reductions <= k * dimension
            assert basis.slot_writes - writes <= k * dimension
        lines.append(
            f"p={p}, k={k}: reductions={basis.row_reductions}, writes={basis.slot_writes}, "
            f"max_pending={basis.max_pending}, per-append bounds passed"
        )
    output = "\n".join(lines) + "\n"
    Path(__file__).with_name("benchmark_results.txt").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
