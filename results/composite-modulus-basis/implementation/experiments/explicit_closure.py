"""Scratch validation of a timestamped p-adic echelon table (stdlib only)."""

from collections import deque
from itertools import product
import random


class PrimePowerBasis:
    def __init__(self, p, k, d):
        self.p, self.k, self.d = p, k, d
        self.mod = p**k
        self.powers = [p**v for v in range(k + 1)]
        self.table = [[None] * k for _ in range(d)]
        self.updates = self.reductions = self.tasks = 0

    def valuation(self, value):
        v = 0
        while value % self.p == 0:
            value //= self.p
            v += 1
        return v

    def insert(self, vector, timestamp):
        queue = deque([(list(vector), timestamp)])
        while queue:
            row, tag = queue.popleft()
            self.tasks += 1
            for j in range(self.d):
                if not row[j]:
                    continue
                v = self.valuation(row[j])
                slot = self.table[j][v]
                if slot is None or tag > slot[0]:
                    old = slot
                    # Normalization uses a unit modulo p**k.
                    unit = pow(row[j] // self.powers[v], -1, self.mod)
                    row = [(a * unit) % self.mod for a in row]
                    self.table[j][v] = (tag, row)
                    self.updates += 1
                    multiple = [(a * self.p) % self.mod for a in row]
                    if any(multiple):
                        queue.append((multiple, tag))
                    if old is None:
                        break
                    tag, row = old
                    row = row.copy()
                pivot = self.table[j][v][1]
                factor = row[j] // self.powers[v]
                row = [(a - factor * b) % self.mod for a, b in zip(row, pivot)]
                self.reductions += 1

    def contains(self, vector, left=1):
        row = [a % self.mod for a in vector]
        for j in range(self.d):
            if not row[j]:
                continue
            v = self.valuation(row[j])
            slot = self.table[j][v]
            if slot is None or slot[0] < left:
                return False
            factor = row[j] // self.powers[v]
            row = [(a - factor * b) % self.mod for a, b in zip(row, slot[1])]
        return True


def generated_span(vectors, mod, d):
    span = {(0,) * d}
    for row in vectors:
        span = {
            tuple((x + c * a) % mod for x, a in zip(xrow, row))
            for xrow in span
            for c in range(mod)
        }
    return span


def check_sequence(sequence, p, k):
    d = len(sequence[0])
    mod = p**k
    universe = list(product(range(mod), repeat=d))
    basis = PrimePowerBasis(p, k, d)
    checks = 0
    for right, row in enumerate(sequence, 1):
        basis.insert(row, right)
        for left in range(1, right + 1):
            span = generated_span(sequence[left - 1 : right], mod, d)
            for x in universe:
                actual = basis.contains(x, left)
                expected = x in span
                assert actual == expected, (p, k, sequence, left, right, x, expected, basis.table)
                checks += 1
            slots = sum(s is not None and s[0] >= left for col in basis.table for s in col)
            assert len(span) == p**slots, (p, k, sequence, left, right, len(span), slots)
    return checks


def main():
    checks = sequences = 0
    for p, k, d, length in [(2, 2, 2, 3), (2, 1, 2, 4), (2, 3, 1, 4)]:
        universe = list(product(range(p**k), repeat=d))
        for sequence in product(universe, repeat=length):
            checks += check_sequence(sequence, p, k)
            sequences += 1
        print("exhaustive", p, k, d, length, "passed", flush=True)
    rng = random.Random(20260911)
    for p, k, d, count in [(2, 2, 3, 150), (2, 3, 2, 150), (3, 2, 2, 150), (3, 1, 3, 100)]:
        for _ in range(count):
            sequence = [tuple(rng.randrange(p**k) for _ in range(d)) for _ in range(6)]
            checks += check_sequence(sequence, p, k)
            sequences += 1
        print("random", p, k, d, count, "passed", flush=True)
    print(f"PASS: {sequences} sequences, {checks} membership checks", flush=True)


if __name__ == "__main__":
    main()
