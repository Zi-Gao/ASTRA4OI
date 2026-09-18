"""Deterministic benchmark inputs; generation and oracle work are never timed."""

from array import array
from dataclasses import asdict, dataclass
import hashlib
import math
from pathlib import Path
import random

from verify import LatticeOracle


@dataclass(frozen=True)
class Case:
    name: str
    n: int
    d: int
    q: int
    factors: tuple
    distribution: str = "uniform"
    seed: int = 20260917


MANY = ((2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1))


def cases(profile):
    if profile == "smoke":
        return [Case("binary", 128, 32, 256, ((2, 1),)),
                Case("square", 160, 8, 320, ((2, 2),)),
                Case("coupled-crt", 160, 8, 320, ((2, 3), (3, 2)), "coupled"),
                Case("word-boundary", 128, 8, 256, ((4294967291, 1),))]
    if profile == "standard":
        return [Case("binary-d64", 20000, 64, 20000, ((2, 1),)),
                Case("prime-d32", 10000, 32, 20000, ((998244353, 1),)),
                Case("square-d32", 20000, 32, 20000, ((2, 2),)),
                Case("deep-power-d24", 12000, 24, 24000, ((2, 16),)),
                Case("odd-power-d24", 12000, 24, 24000, ((3, 10),)),
                Case("crt-d32", 12000, 32, 24000, ((2, 3), (3, 2))),
                Case("many-primes-d24", 12000, 24, 24000, MANY),
                Case("word-boundary-d32", 10000, 32, 20000, ((4294967291, 1),)),
                Case("composite-boundary-d24", 12000, 24, 24000, ((3, 1), (5, 1), (17, 1), (257, 1), (65537, 1))),
                Case("coupled-crt-d32", 12000, 32, 24000, ((2, 3), (3, 2)), "coupled"),
                Case("nonunit-power-d24", 12000, 24, 24000, ((2, 16),), "nonunit"),
                Case("valuation-ladder-d24", 12000, 24, 24000, ((2, 30),), "valuation-ladder"),
                Case("zeros-duplicates-d32", 12000, 32, 24000, ((2, 3), (3, 2)), "zeros-duplicates")]
    if profile == "scaling":
        result = [Case(f"dimension-{d}", 8000, d, 16000, ((2, 2),)) for d in (8, 16, 32, 64)]
        result += [Case(f"exponent-{k}", 8000, 24, 16000, ((2, k),)) for k in (1, 2, 4, 8, 16, 30)]
        result += [Case(f"queries-{q}", 8000, 32, q, ((2, 2),)) for q in (1000, 8000, 64000)]
        # dimension-32 is the n=8000 midpoint; exponent-1 is the w=1 anchor.
        result += [Case(f"length-{n}", n, 32, 16000, ((2, 2),)) for n in (1000, 64000)]
        result += [Case(f"components-{w}", 8000, 24, 16000, MANY[:w]) for w in (2, 4, 8)]
        return result
    if profile == "stress":
        return [Case("n100k-d64-square", 100000, 64, 100000, ((2, 2),)),
                Case("n100k-deep-power", 100000, 32, 100000, ((2, 30),)),
                Case("n100k-many-primes", 100000, 32, 100000, MANY),
                Case("q500k-square", 20000, 32, 500000, ((2, 2),)),
                Case("dimension-128", 20000, 128, 20000, ((2, 2),))]
    raise ValueError(profile)


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while block := stream.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def generate(case, path):
    # Names do not affect randomness: n/d/k/q sweeps share the same seed.
    row_rng = random.Random(case.seed)
    query_rng = random.Random(case.seed + 1)
    modulus = math.prod(p**k for p, k in case.factors)
    p, k = case.factors[0]
    rows = []
    transform = [[int(i == j) if j <= i else row_rng.randrange(modulus)
                  for j in range(case.d)] for i in range(case.d)]
    for i in range(case.n):
        row = [row_rng.randrange(modulus) for _ in range(case.d)]
        if case.distribution == "coupled" and case.d > 1:
            row[-1] = sum(row[:-1]) % modulus
        elif case.distribution == "nonunit":
            row = [x * p % modulus for x in row]
        elif case.distribution == "valuation-ladder":
            level = (i // case.d) % k
            coefficient = p**level
            row = [coefficient * x % modulus for x in transform[i % case.d]]
        elif case.distribution == "zeros-duplicates":
            if i % 4 < 2:
                row = [0] * case.d
            elif i % 4 == 3:
                row = rows[-1]
        rows.append(array("I", row))
    oracle_probes = []
    total_length, min_length, max_length = 0, case.n, 0
    lengths = {"singleton": 0, "2_to_d": 0, "d_plus_1_to_2d": 0, "over_2d": 0}
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as stream:
        stream.write(f"{case.n} {case.d} {modulus} {case.q}\n")
        for row in rows:
            stream.write(" ".join(map(str, row)) + "\n")
        for i in range(case.q):
            right = query_rng.randint(1, case.n)
            kind = query_rng.randrange(4)
            if i < 8:
                length = query_rng.randint(1, min(right, 4))
            elif kind == 0:
                length = 1
            elif kind == 1:
                length = query_rng.randint(1, min(right, case.d))
            elif kind == 2:
                length = query_rng.randint(1, min(right, 2 * case.d))
            else:
                length = query_rng.randint(1, right)
            left = right - length + 1
            if i % 2:
                target = [0] * case.d
                for _ in range(3):
                    row = rows[query_rng.randrange(left - 1, right)]
                    coefficient = query_rng.randrange(modulus)
                    target = [(a + coefficient * b) % modulus for a, b in zip(target, row)]
            else:
                target = [query_rng.randrange(modulus) for _ in range(case.d)]
                if case.distribution == "coupled" and case.d > 1:
                    target[-1] = (sum(target[:-1]) + 1) % modulus
                elif case.distribution == "nonunit":
                    target = [x * p % modulus for x in target]
                    target[-1] = (target[-1] + 1) % modulus
            stream.write(f"{left} {right} " + " ".join(map(str, target)) + "\n")
            if i < 8:
                answer = LatticeOracle(rows[left - 1:right], modulus, case.d).contains(target)
                oracle_probes.append({"query_index": i, "expected": answer})
            total_length += length
            min_length, max_length = min(min_length, length), max(max_length, length)
            bucket = "singleton" if length == 1 else "2_to_d" if length <= case.d else "d_plus_1_to_2d" if length <= 2 * case.d else "over_2d"
            lengths[bucket] += 1
    return {**asdict(case), "modulus": modulus, "K": sum(k for _, k in case.factors),
            "w": len(case.factors), "sha256": file_hash(path), "input_bytes": path.stat().st_size,
            "length_min": min_length, "length_max": max_length,
            "length_mean": total_length / case.q if case.q else 0, "length_histogram": lengths,
            "oracle_probes": oracle_probes,
            "guaranteed_yes_rule": "every odd zero-based query index",
            "guaranteed_no_rule": "every even zero-based query index" if case.distribution in ("coupled", "nonunit") else None}
