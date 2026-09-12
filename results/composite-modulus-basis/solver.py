"""Range module membership over Z/mZ, using timestamped p-adic echelon tables.

Input: n d m q; n vectors; q lines containing l r x_1 ... x_d.
Indices are one-based and inclusive. Output YES / NO.

Arithmetic bound for p**k: O(n*k*d**2 + q*d**2), plus heap,
valuation, and unit-inversion costs detailed in SOLUTION.md.
Only Python's standard library is required.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import heapq
import math
import sys
from typing import Iterable, Sequence


@dataclass(frozen=True, slots=True)
class Pivot:
    timestamp: int
    level: int
    row: tuple[int, ...]


def trial_factorization(modulus: int) -> list[tuple[int, int]]:
    """Correct but intentionally simple: O(sqrt(modulus)) trial divisions."""
    if modulus < 1:
        raise ValueError("modulus must be positive")
    result = []
    p = 2
    remaining = modulus
    while p * p <= remaining:
        if remaining % p == 0:
            k = 0
            while remaining % p == 0:
                remaining //= p
                k += 1
            result.append((p, k))
        p = 3 if p == 2 else p + 2
    if remaining > 1:
        result.append((remaining, 1))
    return result


def factorization(modulus: int, factors=None) -> list[tuple[int, int]]:
    """Supplied factors MUST be a prime factorization; primality is a contract.

    Product, positivity, and distinctness are checked. Trial factorization is
    avoided when the caller already knows the prime factors of a large modulus.
    """
    if modulus < 1:
        raise ValueError("modulus must be positive")
    if factors is None:
        return trial_factorization(modulus)
    result = list(factors)
    if any(p < 2 or k < 1 for p, k in result):
        raise ValueError("factors must contain positive prime powers")
    if len({p for p, _ in result}) != len(result):
        raise ValueError("prime factors must be distinct")
    if math.prod(p**k for p, k in result) != modulus:
        raise ValueError("factorization does not multiply to the modulus")
    return result


class PrimePowerBasis:
    """Current-prefix suffix queries. The caller must supply a prime p."""

    def __init__(self, p: int, k: int, dimension: int):
        if p < 2 or k < 1 or dimension < 1:
            raise ValueError("invalid prime power or dimension")
        self.p, self.k, self.d = p, k, dimension
        self.modulus = p**k
        self.powers = [p**v for v in range(k + 1)]
        self.table: list[list[Pivot | None]] = [[None] * k for _ in range(dimension)]
        self.length = 0
        self.row_reductions = self.slot_writes = self.heap_pops = 0
        self.max_pending = 0

    def valuation(self, value: int) -> int:
        """value is a nonzero residue; O(log(k+1)) divisibility tests."""
        if self.p == 2:
            return (value & -value).bit_length() - 1
        low, high = 0, self.k
        while high - low > 1:
            mid = (low + high) // 2
            if value % self.powers[mid] == 0:
                low = mid
            else:
                high = mid
        return low

    def _subtract(self, row, pivot: Pivot, column: int, valuation: int):
        factor = row[column] // self.powers[valuation]
        self.row_reductions += 1
        return tuple((a - factor * b) % self.modulus for a, b in zip(row, pivot.row))

    def append(self, vector: Sequence[int]) -> None:
        if len(vector) != self.d:
            raise ValueError("wrong vector dimension")
        self.length += 1
        timestamp = self.length
        row = tuple(a % self.modulus for a in vector)
        # Unique (timestamp, level) keys. At most k pending rows at a time.
        pending = []
        for level in range(self.k):
            if not any(row):
                break
            heapq.heappush(pending, (-timestamp, level, 0, row))
            row = tuple(a * self.p % self.modulus for a in row)
        self.max_pending = max(self.max_pending, len(pending))

        while pending:
            minus_tag, level, start_column, row = heapq.heappop(pending)
            tag = -minus_tag
            self.heap_pops += 1
            for j in range(start_column, self.d):
                if row[j] == 0:
                    continue
                v = self.valuation(row[j])
                old = self.table[j][v]
                # Proven in SOLUTION.md: distinct retained p-levels of one
                # timestamp have distinct leading positions modulo newer rows.
                assert old is None or old.timestamp != tag
                if old is None or tag > old.timestamp:
                    inverse = pow(row[j] // self.powers[v], -1, self.modulus)
                    pivot = Pivot(tag, level, tuple(a * inverse % self.modulus for a in row))
                    self.table[j][v] = pivot
                    self.slot_writes += 1
                    if old is not None:
                        residual = self._subtract(old.row, pivot, j, v)
                        if any(residual):
                            # Requeue, rather than immediately following an
                            # older row: all newer timestamps must settle first.
                            heapq.heappush(pending, (-old.timestamp, old.level, j + 1, residual))
                    break
                row = self._subtract(row, old, j, v)

    def snapshot(self):
        """Copy O(d*k) references; immutable Pivot objects/rows are shared."""
        return tuple(tuple(column) for column in self.table)

    def contains(self, vector: Sequence[int], left: int = 1, table=None) -> bool:
        if len(vector) != self.d:
            raise ValueError("wrong vector dimension")
        if table is None:
            table = self.table
        row = [a % self.modulus for a in vector]
        for j in range(self.d):
            if row[j] == 0:
                continue
            v = self.valuation(row[j])
            pivot = table[j][v]
            if pivot is None or pivot.timestamp < left:
                return False
            factor = row[j] // self.powers[v]
            row = [(a - factor * b) % self.modulus for a, b in zip(row, pivot.row)]
        return True

    def span_size(self, left: int = 1, table=None) -> int:
        if table is None:
            table = self.table
        count = sum(pivot is not None and pivot.timestamp >= left for col in table for pivot in col)
        return self.p**count


class RangeBasis:
    """Append vectors and query any past [left, right] using prefix snapshots."""

    def __init__(self, modulus: int, dimension: int, *, factors=None):
        if dimension < 1:
            raise ValueError("dimension must be positive")
        self.modulus, self.d, self.length = modulus, dimension, 0
        self.bases = [PrimePowerBasis(p, k, dimension) for p, k in factorization(modulus, factors)]
        self.versions = []

    def append(self, vector: Sequence[int]) -> None:
        if len(vector) != self.d:
            raise ValueError("wrong vector dimension")
        for basis in self.bases:
            basis.append(vector)
        self.versions.append(tuple(basis.snapshot() for basis in self.bases))
        self.length += 1

    def contains(self, left: int, right: int, vector: Sequence[int]) -> bool:
        if not 1 <= left <= right <= self.length:
            raise ValueError("invalid interval")
        if len(vector) != self.d:
            raise ValueError("wrong vector dimension")
        return all(
            basis.contains(vector, left, table)
            for basis, table in zip(self.bases, self.versions[right - 1])
        )

    def span_size(self, left: int, right: int) -> int:
        if not 1 <= left <= right <= self.length:
            raise ValueError("invalid interval")
        return math.prod(
            basis.span_size(left, table)
            for basis, table in zip(self.bases, self.versions[right - 1])
        )


def solve_offline(
    vectors: Sequence[Sequence[int]], modulus: int,
    queries: Iterable[tuple[int, int, Sequence[int]]], *, factors=None,
) -> list[bool]:
    """Bucket queries by right endpoint; stores only the current tables."""
    if not vectors or not vectors[0]:
        raise ValueError("at least one vector and one coordinate are required")
    n, dimension = len(vectors), len(vectors[0])
    if any(len(row) != dimension for row in vectors):
        raise ValueError("inconsistent vector dimensions")
    bases = [PrimePowerBasis(p, k, dimension) for p, k in factorization(modulus, factors)]
    buckets = [[] for _ in range(n + 1)]
    answers = []
    for index, (left, right, vector) in enumerate(queries):
        if not 1 <= left <= right <= n or len(vector) != dimension:
            raise ValueError("invalid query")
        buckets[right].append((index, left, vector))
        answers.append(False)
    for right, row in enumerate(vectors, 1):
        for basis in bases:
            basis.append(row)
        for index, left, target in buckets[right]:
            answers[index] = all(basis.contains(target, left) for basis in bases)
    return answers


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="use prefix snapshots instead of offline bucketing")
    parser.add_argument("--factors", help="known prime factorization, e.g. 2:2,3:1; supplied bases must be prime")
    args = parser.parse_args()
    values = list(map(int, sys.stdin.buffer.read().split()))
    if len(values) < 4:
        parser.error("expected n d m q, followed by vectors and queries")
    n, d, modulus, q = values[:4]
    if n < 1 or d < 1 or modulus < 1 or q < 0 or len(values) != 4 + n * d + q * (d + 2):
        parser.error("invalid dimensions or input length")
    cursor = 4
    vectors = [tuple(values[cursor + i*d:cursor + (i+1)*d]) for i in range(n)]
    cursor += n*d
    queries = []
    for _ in range(q):
        queries.append((values[cursor], values[cursor+1], tuple(values[cursor+2:cursor+d+2])))
        cursor += d+2
    try:
        factors = None if args.factors is None else [tuple(map(int, part.split(":"))) for part in args.factors.split(",")]
        if args.online:
            basis = RangeBasis(modulus, d, factors=factors)
            for row in vectors:
                basis.append(row)
            answers = [basis.contains(left, right, x) for left, right, x in queries]
        else:
            answers = solve_offline(vectors, modulus, queries, factors=factors)
    except (ValueError, TypeError) as error:
        parser.error(str(error))
    sys.stdout.write("".join("YES\n" if result else "NO\n" for result in answers))


if __name__ == "__main__":
    main()
