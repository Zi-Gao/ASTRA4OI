"""Seeded tests up to 31-bit primes and 120-bit composite moduli.

From implementation/, run through test_solver.py, or directly with: python3 -m tests.large_moduli
The lattice oracle never calls the production solver to obtain an answer.
"""

from itertools import product
from math import gcd, isqrt, prod
import random
import time

from solver import RangeBasis, solve_offline
from tests.oracles import LatticeOracle


SEED = 20260915
FACTORIZATIONS = (
    ((17, 1),),
    ((97, 2),),
    ((257, 4),),
    ((65537, 1),),
    ((65537, 3),),
    ((998244353, 1),),
    ((998244353, 2),),
    ((1000000007, 3),),
    ((2147483647, 2),),
    ((2, 64),),
    ((3, 20),),
    ((2, 12), (97, 3), (65537, 1)),
    ((998244353, 2), (1000000007, 2)),
)


def certify_test_primes():
    """Trial division independently verifies every fixed prime (at most 2^31-1)."""
    primes = sorted({p for factors in FACTORIZATIONS for p, _ in factors})
    for p in primes:
        assert p >= 2
        assert p == 2 or p % 2 != 0
        assert all(p % divisor for divisor in range(3, isqrt(p) + 1, 2)), p
    return primes


def check_oracle_on_small_spans(rng):
    checks = 0
    for modulus in (1, 2, 4, 6, 8, 9, 12):
        for dimension in (1, 2):
            for _ in range(12):
                sequence = [tuple(rng.randrange(modulus) for _ in range(dimension)) for _ in range(3)]
                span = {(0,) * dimension}
                for vector in sequence:
                    span = {
                        tuple((x + c * a) % modulus for x, a in zip(old, vector))
                        for old in span for c in range(modulus)
                    }
                oracle = LatticeOracle(sequence, modulus, dimension)
                assert oracle.span_size == len(span)
                for target in product(range(modulus), repeat=dimension):
                    assert oracle.contains(target) == (target in span)
                    checks += 1
    return checks


def assert_append_bounds(basis, vector):
    before = [
        (b.row_reductions, b.slot_writes, b.heap_pops, b.column_visits, b.initial_row_passes)
        for b in basis.bases
    ]
    basis.append(vector)
    for b, old in zip(basis.bases, before):
        reductions, writes, pops, visits, initial = (
            value - prior for value, prior in zip(
                (b.row_reductions, b.slot_writes, b.heap_pops, b.column_visits, b.initial_row_passes),
                old,
            )
        )
        assert visits <= b.k * b.d
        assert reductions <= visits and writes <= visits
        assert pops <= b.k * (b.d + 1) and b.max_pending <= b.k
        assert initial <= b.k
        assert (initial + reductions + writes) * b.d <= 3 * b.k * b.d**2


def targets_for(sequence, modulus, rng):
    dimension = len(sequence[0])
    targets = [(0,) * dimension, tuple(sequence[0])]
    for _ in range(3):
        coefficients = [rng.randrange(-modulus, modulus) for _ in sequence]
        targets.append(tuple(
            sum(c * a[j] for c, a in zip(coefficients, sequence)) % modulus
            for j in range(dimension)
        ))
    for _ in range(4):
        targets.append(tuple(rng.randrange(-modulus, 2 * modulus) for _ in range(dimension)))
    for j in (0, dimension - 1):
        targets.append(tuple(int(i == j) for i in range(dimension)))
    return targets


def structured_sequence(modulus, factors, dimension, rng):
    """Full, deficient, zero-divisor, and changing-suffix cases, not only random full rank."""
    prime = factors[0][0]
    hidden = [tuple(rng.randrange(modulus) for _ in range(dimension)) for _ in range(max(1, dimension // 2))]
    rows = []
    for i in range(24):
        if i % 7 == 0:
            row = (0,) * dimension
        elif i % 7 == 1 and rows:
            row = rows[-1]
        elif i < 8:
            # A coupled annihilator relation in the first two coordinates.
            row = tuple(prime if j == 0 else 1 if j == 1 else 0 for j in range(dimension))
            if i % 2:
                row = tuple(rng.randrange(modulus) for _ in range(dimension))
        else:
            coefficients = [rng.randrange(modulus) for _ in hidden]
            row = tuple(sum(c * a[j] for c, a in zip(coefficients, hidden)) % modulus for j in range(dimension))
            divisor = prod(p ** rng.randrange(k + 1) for p, k in factors)
            row = tuple(divisor * a % modulus for a in row)
            # Newer suffixes cannot use the last coordinate.
            if i >= 16:
                row = row[:-1] + (0,)
        # Also exercise negative and noncanonical input representatives.
        rows.append(tuple(a + rng.randrange(-2, 3) * modulus for a in row))
    return rows


def check_lattice_cases(factors, rng, counts):
    modulus = prod(p**k for p, k in factors)
    for dimension in (2, 4, 8, 12):
        sequence = structured_sequence(modulus, factors, dimension, rng)
        basis = RangeBasis(modulus, dimension, factors=factors)
        queries, expected_answers = [], []
        for right, vector in enumerate(sequence, 1):
            assert_append_bounds(basis, vector)
            # Every prefix and single-row interval, plus changing and historical suffixes.
            lefts = {1, right, max(1, right - dimension // 2), rng.randrange(1, right + 1)}
            for left in sorted(lefts):
                interval = sequence[left - 1:right]
                oracle = LatticeOracle(interval, modulus, dimension)
                assert basis.span_size(left, right) == oracle.span_size
                counts["lattice_intervals"] += 1
                for target in targets_for(interval, modulus, rng):
                    expected = oracle.contains(target)
                    query = (left, right, target)
                    assert basis.contains(*query) == expected, (factors, dimension, query, expected)
                    queries.append(query)
                    expected_answers.append(expected)
                    counts["yes" if expected else "no"] += 1
        order = list(range(len(queries)))
        rng.shuffle(order)
        for index in order:
            assert basis.contains(*queries[index]) == expected_answers[index], ("historical", factors, queries[index])
        assert solve_offline(sequence, modulus, queries, factors=factors) == expected_answers
        counts["membership_assertions"] += 3 * len(queries)
        counts["sequences"] += 1


def check_diagonal_cases(factors, rng, counts):
    """Independent analytic truth after a known invertible change of coordinates.

    Generators c_i*e_axis span the product of coordinate ideals gcd(m,c_i).
    Apply a fixed unimodular matrix to both inputs and targets.  Expected
    membership and size still follow from those gcds, without any elimination.
    """
    modulus, dimension, length = prod(p**k for p, k in factors), 8, 32
    transform = [[int(i == j) for j in range(dimension)] for i in range(dimension)]
    for _ in range(4 * dimension):
        a, b = rng.sample(range(dimension), 2)
        coefficient = rng.randrange(-5, 6)
        transform[a] = [x + coefficient * y for x, y in zip(transform[a], transform[b])]
        transform[a], transform[b] = transform[b], transform[a]

    def encode(row):
        return tuple(sum(row[i] * transform[i][j] for i in range(dimension)) % modulus for j in range(dimension))

    latent, sequence = [], []
    basis = RangeBasis(modulus, dimension, factors=factors)
    queries, answers = [], []
    for right in range(1, length + 1):
        axis = rng.randrange(dimension)
        coefficient = prod(p ** rng.randrange(k + 1) for p, k in factors) * rng.randrange(1, 20)
        row = tuple(coefficient if i == axis else 0 for i in range(dimension))
        latent.append(row)
        sequence.append(encode(row))
        assert_append_bounds(basis, sequence[-1])
        for left in sorted({1, right, rng.randrange(1, right + 1)}):
            divisors = [gcd(modulus, *(a[j] for a in latent[left - 1:right])) for j in range(dimension)]
            expected_size = prod(modulus // g for g in divisors)
            assert basis.span_size(left, right) == expected_size
            oracle = LatticeOracle(sequence[left - 1:right], modulus, dimension)
            assert oracle.span_size == expected_size
            counts["analytic_intervals"] += 1
            positive = tuple(g * rng.randrange(modulus) % modulus for g in divisors)
            targets = [positive]
            for j, g in enumerate(divisors):
                if g > 1:
                    negative = list(positive)
                    negative[j] = (negative[j] + 1) % modulus
                    targets.append(tuple(negative))
            targets.append(tuple(rng.randrange(modulus) for _ in range(dimension)))
            for target in targets:
                expected = all(a % g == 0 for a, g in zip(target, divisors))
                query = (left, right, encode(target))
                assert oracle.contains(query[2]) == expected, ("lattice vs analytic", factors, query)
                counts["analytic_oracle_assertions"] += 1
                assert basis.contains(*query) == expected, ("diagonal", factors, query)
                queries.append(query)
                answers.append(expected)
                counts["yes" if expected else "no"] += 1
    for query, expected in reversed(list(zip(queries, answers))):
        assert basis.contains(*query) == expected
    assert solve_offline(sequence, modulus, queries, factors=factors) == answers
    counts["membership_assertions"] += 3 * len(queries)
    counts["sequences"] += 1


def check_one_dimension(factors, rng, counts):
    modulus, length = prod(p**k for p, k in factors), 24
    sequence = [
        (prod(p ** rng.randrange(k + 1) for p, k in factors) * rng.randrange(-100, 100),)
        for _ in range(length)
    ]
    basis = RangeBasis(modulus, 1, factors=factors)
    queries, answers = [], []
    for right, row in enumerate(sequence, 1):
        assert_append_bounds(basis, row)
        for left in range(1, right + 1):
            divisor = gcd(modulus, *(a[0] for a in sequence[left - 1:right]))
            assert basis.span_size(left, right) == modulus // divisor
            counts["gcd_intervals"] += 1
            for target in (0, 1, divisor, divisor - 1, -divisor, rng.randrange(modulus)):
                expected = target % divisor == 0
                query = (left, right, (target,))
                assert basis.contains(*query) == expected, ("gcd", factors, query)
                queries.append(query)
                answers.append(expected)
                counts["yes" if expected else "no"] += 1
    for query, expected in reversed(list(zip(queries, answers))):
        assert basis.contains(*query) == expected
    assert solve_offline(sequence, modulus, queries, factors=factors) == answers
    counts["membership_assertions"] += 3 * len(queries)
    counts["sequences"] += 1


def main():
    if not __debug__:
        raise RuntimeError("Tests require assertions; do not use python -O")
    started = time.perf_counter()
    rng = random.Random(SEED)
    counts = dict.fromkeys(("sequences", "lattice_intervals", "analytic_intervals", "gcd_intervals", "membership_assertions", "analytic_oracle_assertions", "yes", "no"), 0)
    primes = certify_test_primes()
    print(f"Large-modulus seed: {SEED}; independently trial-checked primes: {primes}", flush=True)
    checks = check_oracle_on_small_spans(rng)
    print(f"PASS lattice oracle vs coefficient enumeration: {checks} targets", flush=True)
    for factors in FACTORIZATIONS:
        before_yes, before_no = counts["yes"], counts["no"]
        check_lattice_cases(factors, rng, counts)
        check_diagonal_cases(factors, rng, counts)
        check_one_dimension(factors, rng, counts)
        assert counts["yes"] > before_yes and counts["no"] > before_no
        modulus = prod(p**k for p, k in factors)
        print(f"PASS factors={factors}; modulus_bits={modulus.bit_length()}; YES={counts['yes'] - before_yes}, NO={counts['no'] - before_no}", flush=True)
    print("PASS large-modulus suite:", counts, flush=True)
    print(f"Large-modulus elapsed: {time.perf_counter() - started:.3f} seconds", flush=True)
    return counts


if __name__ == "__main__":
    main()
