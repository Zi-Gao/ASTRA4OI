"""Independent finite-span oracles, persistence checks, and ring reductions."""

from itertools import product
from pathlib import Path
import random
import subprocess
import sys
import time

from solver import PrimePowerBasis, RangeBasis, solve_offline, trial_factorization


COUNTS = {"sequences": 0, "intervals": 0, "membership_assertions": 0, "ring_assertions": 0}


def extend_span(span, vector, modulus):
    """Enumerate every scalar. No elimination or p-adic logic in this oracle."""
    return {
        tuple((x + coefficient * a) % modulus for x, a in zip(old, vector))
        for old in span
        for coefficient in range(modulus)
    }


def check_sequence(sequence, modulus, rng):
    dimension = len(sequence[0])
    universe = list(product(range(modulus), repeat=dimension))
    online = RangeBasis(modulus, dimension)
    cases = []
    for right, vector in enumerate(sequence, 1):
        online.append(vector)
        span = {(0,) * dimension}
        for left in range(right, 0, -1):
            span = extend_span(span, sequence[left - 1], modulus)
            assert online.span_size(left, right) == len(span), (sequence, modulus, left, right)
            COUNTS["intervals"] += 1
            for target in universe:
                expected = target in span
                assert online.contains(left, right, target) == expected, (sequence, modulus, left, right, target)
                cases.append(((left, right, target), expected))
                COUNTS["membership_assertions"] += 1
    # Re-read old versions after all later appends, in an unrelated query order.
    rng.shuffle(cases)
    for (left, right, target), expected in cases:
        assert online.contains(left, right, target) == expected, ("snapshot changed", sequence, left, right, target)
        COUNTS["membership_assertions"] += 1
    offline = solve_offline(sequence, modulus, [query for query, _ in cases])
    assert offline == [expected for _, expected in cases], ("offline mismatch", sequence, modulus)
    COUNTS["membership_assertions"] += len(cases)
    COUNTS["sequences"] += 1


def check_metadata_and_operation_bound():
    """Check the stronger cyclic-quotient invariant against exact small spans."""
    rng = random.Random(2026091201)
    for p, k, dimension in [(2, 2, 3), (2, 3, 2), (3, 2, 2)]:
        modulus = p**k
        for _ in range(80):
            basis = PrimePowerBasis(p, k, dimension)
            sequence = []
            for timestamp in range(1, 8):
                vector = tuple(rng.randrange(modulus) for _ in range(dimension))
                sequence.append(vector)
                old_counts = basis.row_reductions, basis.slot_writes, basis.heap_pops
                basis.append(vector)
                assert basis.row_reductions - old_counts[0] <= k * dimension
                assert basis.slot_writes - old_counts[1] <= k * dimension
                assert basis.heap_pops - old_counts[2] <= k * (dimension + 1)
                assert basis.max_pending <= k
                newer = {(0,) * dimension}
                for t in range(timestamp, 0, -1):
                    current = extend_span(newer, sequence[t - 1], modulus)
                    ratio, h = len(current) // len(newer), 0
                    while ratio > 1:
                        assert ratio % p == 0
                        ratio //= p
                        h += 1
                    pivots = [b for col in basis.table for b in col if b is not None and b.timestamp == t]
                    assert sorted(b.level for b in pivots) == list(range(h))
                    for b in pivots:
                        assert any(
                            tuple((x - unit * p**b.level * a) % modulus for x, a in zip(b.row, sequence[t - 1])) in newer
                            for unit in range(1, modulus) if unit % p != 0
                        ), ("cyclic quotient invariant", p, k, sequence, b)
                    newer = current
    print("PASS stronger timestamp/level invariants and per-append operation bounds", flush=True)


def compare_large_structured_cases():
    # The explicitly closed prototype is an additional algorithmic cross-check;
    # small-case correctness above uses an independent coefficient oracle.
    from experiment import PrimePowerBasis as ClosureBasis
    rng = random.Random(2026091202)
    for _ in range(1200):
        p, k, dimension = rng.choice([2, 3, 5, 7]), rng.randrange(1, 9), rng.randrange(1, 10)
        modulus = p**k
        hidden = [tuple(rng.randrange(modulus) for _ in range(dimension)) for _ in range(rng.randrange(1, dimension + 1))]
        fast, closed = PrimePowerBasis(p, k, dimension), ClosureBasis(p, k, dimension)
        for timestamp in range(1, 2 * dimension + 4):
            coefficients = [rng.randrange(modulus) * p**rng.randrange(k) % modulus for _ in hidden]
            vector = tuple(sum(c * a[j] for c, a in zip(coefficients, hidden)) % modulus for j in range(dimension))
            reductions, writes = fast.row_reductions, fast.slot_writes
            fast.append(vector)
            closed.insert(vector, timestamp)
            assert fast.row_reductions - reductions <= k * dimension
            assert fast.slot_writes - writes <= k * dimension
            fast_tags = [[b.timestamp if b else -1 for b in col] for col in fast.table]
            closed_tags = [[b[0] if b else -1 for b in col] for col in closed.table]
            assert fast_tags == closed_tags
    print("PASS 1200 structured random comparisons with explicit closure algorithm", flush=True)


def ring_span(vectors, elements, dimension, add, multiply, zero):
    span = {(zero,) * dimension}
    for vector in vectors:
        span = {
            tuple(add(x, multiply(c, a)) for x, a in zip(old, vector))
            for old in span for c in elements
        }
    return span


def check_finite_rings():
    rng = random.Random(2026091203)

    def square_zero_product(a, b):
        # F2[e,f]/(e^2,ef,f^2), coordinates packed into bits.
        return ((a & 1) * (b & 1)) | ((((a & 1) * ((b >> 1) & 1)) ^ (((a >> 1) & 1) * (b & 1))) << 1) | ((((a & 1) * ((b >> 2) & 1)) ^ (((a >> 2) & 1) * (b & 1))) << 2)

    rings = [
        ("F2[e,f]/(e^2,ef,f^2)", 8, 2, [1, 2, 4],
         lambda a, b: a ^ b, square_zero_product,
         lambda a: (a & 1, (a >> 1) & 1, (a >> 2) & 1)),
        ("Z4[e]/(e^2)", 16, 4, [1, 4],
         lambda a, b: (a % 4 + b % 4) % 4 + 4 * ((a // 4 + b // 4) % 4),
         lambda a, b: ((a % 4) * (b % 4)) % 4 + 4 * (((a % 4) * (b // 4) + (a // 4) * (b % 4)) % 4),
         lambda a: (a % 4, a // 4)),
        ("Z4 x F2 (unequal additive exponents)", 8, 4, [1, 4],
         lambda a, b: (a % 4 + b % 4) % 4 + 4 * ((a // 4 + b // 4) % 2),
         lambda a, b: ((a % 4) * (b % 4)) % 4 + 4 * ((a // 4) * (b // 4)),
         lambda a: (a % 4, 2 * (a // 4))),
    ]
    for name, size, modulus, generators, add, multiply, embed in rings:
        dimension, block = 2, len(generators)
        for _ in range(40):
            sequence = [tuple(rng.randrange(size) for _ in range(dimension)) for _ in range(4)]
            basis = RangeBasis(modulus, dimension * block)
            for vector in sequence:
                for generator in generators:
                    basis.append(tuple(z for a in vector for z in embed(multiply(generator, a))))
            for left in range(1, 5):
                for right in range(left, 5):
                    span = ring_span(sequence[left - 1:right], range(size), dimension, add, multiply, 0)
                    assert basis.span_size((left - 1) * block + 1, right * block) == len(span)
                    for target in product(range(size), repeat=dimension):
                        flat = tuple(z for a in target for z in embed(a))
                        assert basis.contains((left - 1) * block + 1, right * block, flat) == (target in span)
                        COUNTS["ring_assertions"] += 1
        print("PASS general ring reduction:", name, flush=True)


def check_interfaces():
    here = Path(__file__).resolve().parent
    data, expected = (here / "example.in").read_bytes(), (here / "example.out").read_bytes()
    for flags in [[], ["--online"], ["--factors", "2:2"]]:
        process = subprocess.run([sys.executable, str(here / "solver.py"), *flags], input=data, capture_output=True, check=True)
        assert process.stdout == expected
    assert trial_factorization(1) == []
    assert trial_factorization(360) == [(2, 3), (3, 2), (5, 1)]
    known = RangeBasis(12, 2, factors=[(2, 2), (3, 1)])
    known.append((-1, 14))
    assert known.contains(1, 1, (11, 2))
    assert not known.contains(1, 1, (0, 1))
    for left, right in [(0, 1), (1, 2), (2, 1)]:
        try:
            known.contains(left, right, (0, 0))
        except ValueError:
            pass
        else:
            raise AssertionError("invalid interval accepted")
    empty = RangeBasis(1, 3)
    empty.append((14, -12, 999))
    assert empty.contains(1, 1, (5, 6, 7)) and empty.span_size(1, 1) == 1
    # Explicit regressions for the two naive counterexamples.
    annihilator = RangeBasis(4, 2)
    annihilator.append((2, 1))
    assert annihilator.contains(1, 1, (0, 2))
    times = RangeBasis(4, 1)
    times.append((1,)); times.append((2,))
    assert times.contains(1, 2, (1,)) and not times.contains(2, 2, (1,))
    print("PASS CLI, known factorization, noncanonical coordinates, invalid intervals, and regressions", flush=True)


def main():
    started = time.perf_counter()
    rng = random.Random(20260912)
    check_interfaces()
    for modulus, dimension, length in [(4, 2, 3), (8, 1, 4), (2, 2, 4), (6, 1, 3), (12, 1, 2)]:
        universe = list(product(range(modulus), repeat=dimension))
        for sequence in product(universe, repeat=length):
            check_sequence(sequence, modulus, rng)
        print("PASS exhaustive", {"modulus": modulus, "dimension": dimension, "length": length}, flush=True)
    for modulus, dimension, count in [(4, 3, 80), (8, 2, 80), (9, 2, 80), (12, 2, 80), (18, 2, 40), (6, 3, 60), (5, 3, 40), (1, 3, 10)]:
        for _ in range(count):
            sequence = [tuple(rng.randrange(-modulus, 2 * modulus) for _ in range(dimension)) for _ in range(6)]
            check_sequence(sequence, modulus, rng)
        print("PASS random", {"modulus": modulus, "dimension": dimension, "sequences": count}, flush=True)
    check_metadata_and_operation_bound()
    compare_large_structured_cases()
    check_finite_rings()
    print("PASS all tests:", COUNTS, flush=True)
    print(f"Elapsed: {time.perf_counter() - started:.3f} seconds", flush=True)


if __name__ == "__main__":
    main()
