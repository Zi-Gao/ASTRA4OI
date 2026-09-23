#!/usr/bin/env python3
"""Deterministically generate independently-labelled official data."""

from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from dataclasses import asdict, dataclass
import hashlib
import json
import math
from pathlib import Path
import random


@dataclass(frozen=True)
class Case:
    case_id: str
    name: str
    subtask: str
    n: int
    d: int
    factors: tuple[tuple[int, int], ...]
    q: int
    mode: str
    seed: int
    prefix: bool = False

    @property
    def modulus(self) -> int:
        return math.prod(prime**exponent for prime, exponent in self.factors)


CASES = (
    Case("01", "small-p4", "small", 12, 2, ((2, 2),), 32, "exhaustive", 91001),
    Case("02", "small-crt", "small", 14, 3, ((2, 1), (3, 1)), 40, "exhaustive", 91002),
    Case("03", "small-zeros", "small", 30, 4, ((2, 2), (3, 1)), 60, "coupled-zeros", 91003),
    Case("04", "dimension-one-72", "dimension-one", 10_000, 1,
         ((2, 3), (3, 2)), 12_000, "one-dimensional", 91004),
    Case("05", "dimension-one-boundary", "dimension-one", 100_000, 1,
         ((2, 1), (998_244_353, 1)), 100_000, "one-dimensional", 91005),
    Case("06", "prime-local", "prime", 6_000, 16,
         ((998_244_353, 1),), 8_000, "local", 91006),
    Case("07", "prime-coupled", "prime", 5_000, 20,
         ((1_000_000_007, 1),), 7_000, "coupled", 91007),
    Case("08", "squarefree-local", "squarefree", 8_000, 14,
         ((2, 1), (3, 1)), 10_000, "local", 91008),
    Case("09", "squarefree-axis", "squarefree", 7_000, 16,
         ((2, 1), (3, 1), (5, 1), (7, 1)), 9_000, "diagonal", 91009),
    Case("10", "squarefree-zeros", "squarefree", 5_000, 20,
         ((3, 1), (5, 1), (7, 1), (11, 1)), 7_000, "coupled-zeros", 91010),
    Case("11", "prefix-power", "prefix", 8_000, 16,
         ((2, 8),), 10_000, "nonunit", 91011, True),
    Case("12", "prefix-crt", "prefix", 6_500, 20,
         ((2, 3), (3, 2)), 8_500, "diagonal", 91012, True),
    Case("13", "full-padic-local", "full", 7_000, 20,
         ((2, 8),), 9_000, "local", 91013),
    Case("14", "full-crt-coupled", "full", 8_000, 20,
         ((2, 3), (3, 2)), 10_000, "coupled", 91014),
    Case("15", "full-many-primes", "full", 8_000, 18,
         ((2, 1), (3, 1), (5, 1), (7, 1)), 10_000, "diagonal", 91015),
    Case("16", "full-zeros-duplicates", "full", 5_000, 24,
         ((2, 3), (3, 2)), 7_000, "coupled-zeros", 91016),
    Case("17", "full-large-modulus", "full", 5_000, 20,
         ((2, 1), (998_244_353, 1)), 7_000, "nonunit", 91017),
    Case("18", "full-max-nq", "full", 100_000, 2,
         ((2, 2),), 100_000, "diagonal", 91018),
    Case("19", "full-deep-power", "full", 30_000, 20,
         ((3, 8),), 30_000, "diagonal-valuation", 91019),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1 << 20):
            digest.update(block)
    return digest.hexdigest()


def random_unit(rng: random.Random, modulus: int) -> int:
    while True:
        value = rng.randrange(1, modulus)
        if math.gcd(value, modulus) == 1:
            return value


def interval(rng: random.Random, n: int, dimension: int, index: int,
             *, prefix: bool = False, short: bool = False) -> tuple[int, int]:
    if prefix:
        return 0, rng.randrange(n)
    right = rng.randrange(n)
    if short:
        length = rng.randint(1, min(right + 1, max(1, dimension - 1)))
    elif index % 4 == 0:
        length = 1
    elif index % 4 == 1:
        length = rng.randint(1, min(right + 1, max(1, dimension)))
    elif index % 4 == 2:
        length = rng.randint(1, min(right + 1, max(1, 2 * dimension)))
    else:
        length = rng.randint(1, right + 1)
    return right - length + 1, right


def linear_combination(rows: list[list[int]], left: int, right: int,
                       modulus: int, rng: random.Random, query_index: int) -> list[int]:
    dimension = len(rows[0])
    target = [0] * dimension
    if query_index == 0:
        return target
    for _ in range(min(4, right - left + 1)):
        row = rows[rng.randint(left, right)]
        coefficient = rng.randrange(modulus)
        target = [(a + coefficient * b) % modulus for a, b in zip(target, row)]
    return target


def positive_query(answer_rng: random.Random, query_index: int) -> bool:
    # Force both answers to occur, then use an independent random stream so
    # query order itself reveals nothing about the answer.
    if query_index == 0:
        return True
    if query_index == 1:
        return False
    return bool(answer_rng.getrandbits(1))


def closure_states(rows: list[list[int]], left: int, right: int,
                   modulus: int) -> set[tuple[int, ...]]:
    """Independent coefficient closure for deliberately tiny official cases."""
    dimension = len(rows[0])
    reachable = {(0,) * dimension}
    for vector in rows[left:right + 1]:
        expanded = set()
        for state in reachable:
            current = list(state)
            for _ in range(modulus):
                expanded.add(tuple(current))
                current = [(a + b) % modulus for a, b in zip(current, vector)]
        reachable = expanded
    return reachable


def make_exhaustive(case: Case, row_rng: random.Random, query_rng: random.Random,
                    answer_rng: random.Random):
    modulus = case.modulus
    rows = [[row_rng.randrange(modulus) for _ in range(case.d)] for _ in range(case.n)]
    if case.case_id == "01":
        # Explicit p-adic closure and suffix-timestamp traps.
        rows[:5] = [[2, 1], [0, 0], [1, 0], [2, 0], [0, 2]]
    queries = []
    answers = []
    manual = []
    if case.case_id == "01":
        manual = [
            (0, 0, [0, 2]),  # 2*(2,1): requires the p-multiple layer.
            (0, 0, [1, 0]),  # A basic nonmember for the same singleton span.
            (1, 1, [0, 2]),  # A zero generator cannot make a hidden p-torsion target.
            (2, 3, [1, 0]),  # Newer unit plus nonunit; timestamp must be preserved.
            (3, 3, [1, 0]),  # The suffix containing only (2,0) cannot make (1,0).
        ]
    for index in range(case.q):
        if index < len(manual):
            left, right, target = manual[index]
            states = closure_states(rows, left, right, modulus)
        else:
            want_positive = positive_query(answer_rng, index)
            while True:
                left, right = interval(query_rng, case.n, case.d, index,
                                       short=not want_positive)
                states = closure_states(rows, left, right, modulus)
                if want_positive or len(states) < modulus**case.d:
                    break
            if want_positive:
                target = linear_combination(rows, left, right, modulus, query_rng, index)
            else:
                while True:
                    target = [query_rng.randrange(modulus) for _ in range(case.d)]
                    if tuple(target) not in states:
                        break
        answer = tuple(target) in states
        queries.append((left, right, target))
        answers.append(answer)
    return rows, queries, answers


def field_basis(rows: list[list[int]], prime: int) -> list[list[int] | None]:
    dimension = len(rows[0])
    pivots: list[list[int] | None] = [None] * dimension
    for source in rows:
        row = [value % prime for value in source]
        for column in range(dimension):
            if row[column] == 0:
                continue
            if pivots[column] is None:
                inverse = pow(row[column], prime - 2, prime)
                row = [value * inverse % prime for value in row]
                pivots[column] = row
                break
            coefficient = row[column]
            row = [(a - coefficient * b) % prime
                   for a, b in zip(row, pivots[column])]
    return pivots


def field_contains(pivots: list[list[int] | None], target: list[int], prime: int) -> bool:
    row = [value % prime for value in target]
    for column, pivot in enumerate(pivots):
        if row[column] == 0:
            continue
        if pivot is None:
            return False
        coefficient = row[column]
        row = [(a - coefficient * b) % prime for a, b in zip(row, pivot)]
    return True


def make_local(case: Case, row_rng: random.Random, query_rng: random.Random,
               answer_rng: random.Random):
    modulus = case.modulus
    rows = [[row_rng.randrange(modulus) for _ in range(case.d)] for _ in range(case.n)]
    queries = []
    answers = []
    prime = case.factors[0][0]
    for index in range(case.q):
        positive = positive_query(answer_rng, index)
        left, right = interval(query_rng, case.n, case.d, index,
                               prefix=case.prefix, short=not positive)
        if positive:
            target = linear_combination(rows, left, right, modulus, query_rng, index)
        else:
            pivots = field_basis(rows[left:right + 1], prime)
            while True:
                target = [query_rng.randrange(modulus) for _ in range(case.d)]
                if not field_contains(pivots, target, prime):
                    break
        queries.append((left, right, target))
        answers.append(positive)
    return rows, queries, answers


def make_coupled(case: Case, row_rng: random.Random, query_rng: random.Random,
                 answer_rng: random.Random):
    modulus = case.modulus
    weights = [random_unit(row_rng, modulus) for _ in range(case.d - 1)]
    rows = []
    with_zeros = case.mode.endswith("zeros")
    for index in range(case.n):
        if with_zeros and index % 6 == 0:
            row = [0] * case.d
        elif with_zeros and index % 6 == 1 and rows:
            row = rows[-1][:]
        else:
            row = [row_rng.randrange(modulus) for _ in range(case.d - 1)]
            row.append(sum(a * b for a, b in zip(row, weights)) % modulus)
        rows.append(row)

    queries = []
    answers = []
    for index in range(case.q):
        positive = positive_query(answer_rng, index)
        left, right = interval(query_rng, case.n, case.d, index, prefix=case.prefix)
        if positive:
            target = linear_combination(rows, left, right, modulus, query_rng, index)
        else:
            target = [query_rng.randrange(modulus) for _ in range(case.d - 1)]
            target.append((sum(a * b for a, b in zip(target, weights)) + 1) % modulus)
        queries.append((left, right, target))
        answers.append(positive)
    return rows, queries, answers


def make_nonunit(case: Case, row_rng: random.Random, query_rng: random.Random,
                 answer_rng: random.Random):
    modulus = case.modulus
    prime, exponent = case.factors[0]
    blocker = prime**min(2, exponent)
    rows = []
    for _ in range(case.n):
        row = [blocker * row_rng.randrange(modulus // blocker)]
        row.extend(row_rng.randrange(modulus) for _ in range(case.d - 1))
        rows.append(row)
    queries = []
    answers = []
    for index in range(case.q):
        positive = positive_query(answer_rng, index)
        left, right = interval(query_rng, case.n, case.d, index, prefix=case.prefix)
        if positive:
            target = linear_combination(rows, left, right, modulus, query_rng, index)
        else:
            target = [query_rng.randrange(modulus) for _ in range(case.d)]
            target[0] = blocker // prime
        queries.append((left, right, target))
        answers.append(positive)
    return rows, queries, answers


class SegmentGCD:
    def __init__(self, values: list[int], modulus: int):
        size = 1
        while size < len(values):
            size *= 2
        self.size = size
        self.tree = [0] * (2 * size)
        self.tree[size:size + len(values)] = values
        for index in range(size - 1, 0, -1):
            self.tree[index] = math.gcd(self.tree[2 * index], self.tree[2 * index + 1])
        self.modulus = modulus

    def query(self, left: int, right: int) -> int:
        left += self.size
        right += self.size + 1
        result = self.modulus
        while left < right:
            if left & 1:
                result = math.gcd(result, self.tree[left])
                left += 1
            if right & 1:
                right -= 1
                result = math.gcd(result, self.tree[right])
            left //= 2
            right //= 2
        return result


def make_one_dimensional(case: Case, row_rng: random.Random, query_rng: random.Random,
                         answer_rng: random.Random):
    modulus = case.modulus
    prime, exponent = case.factors[0]
    blocker = prime**min(2, exponent)
    values = []
    for index in range(case.n):
        if index % 19 == 0:
            value = 0
        else:
            value = blocker * row_rng.randrange(modulus // blocker)
        values.append(value)
    oracle = SegmentGCD(values, modulus)
    rows = [[value] for value in values]
    queries = []
    answers = []
    for index in range(case.q):
        positive = positive_query(answer_rng, index)
        left, right = interval(query_rng, case.n, 1, index)
        divisor = oracle.query(left, right)
        if positive:
            target = [divisor * query_rng.randrange(modulus // divisor)]
        else:
            target = [divisor // prime if divisor % (prime * prime) == 0 else 1]
            assert divisor > 1
        queries.append((left, right, target))
        answers.append(positive)
    return rows, queries, answers


class SparseGCD:
    def __init__(self, values: list[int]):
        self.levels = [values]
        width = 2
        while width <= len(values):
            previous = self.levels[-1]
            half = width // 2
            self.levels.append([
                math.gcd(previous[index], previous[index + half])
                for index in range(len(values) - width + 1)
            ])
            width *= 2

    def query(self, left: int, right: int) -> int:
        length = right - left
        level = length.bit_length() - 1
        width = 1 << level
        return math.gcd(self.levels[level][left], self.levels[level][right - width])


def invertible_matrix(dimension: int, modulus: int, rng: random.Random) -> list[list[int]]:
    matrix = [[int(row == column) for column in range(dimension)]
              for row in range(dimension)]
    for step in range(6 * dimension):
        first = rng.randrange(dimension)
        second = rng.randrange(dimension - 1)
        if second >= first:
            second += 1
        if step % 5 == 0:
            matrix[first], matrix[second] = matrix[second], matrix[first]
        elif step % 5 == 1:
            unit = random_unit(rng, modulus)
            matrix[first] = [unit * value % modulus for value in matrix[first]]
        else:
            coefficient = rng.randrange(modulus)
            matrix[first] = [(a + coefficient * b) % modulus
                             for a, b in zip(matrix[first], matrix[second])]
    return matrix


def transform(vector: list[int], matrix: list[list[int]], modulus: int) -> list[int]:
    dimension = len(vector)
    return [sum(vector[row] * matrix[row][column] for row in range(dimension)) % modulus
            for column in range(dimension)]


def diagonal_coefficient(case: Case, axis: int, index: int, rng: random.Random) -> int:
    modulus = case.modulus
    prime, exponent = case.factors[0]
    blocker = prime**min(2, exponent)
    if index % 23 == 0:
        return 0
    if axis == 0:
        return blocker * random_unit(rng, modulus) % modulus
    if case.mode.endswith("valuation"):
        prime, exponent = case.factors[0]
        order = (index // case.d + axis) % (exponent + 1)
        if order == exponent:
            return 0
        return pow(prime, order) * random_unit(rng, modulus) % modulus
    if index % 11 == 0:
        return 1
    divisor = 1
    for prime, exponent in case.factors:
        order = rng.randrange(exponent + 1)
        divisor *= prime**order
    if divisor == modulus:
        return 0
    return divisor * random_unit(rng, modulus) % modulus


def make_diagonal(case: Case, row_rng: random.Random, query_rng: random.Random,
                  answer_rng: random.Random):
    modulus = case.modulus
    matrix = invertible_matrix(case.d, modulus, row_rng)
    permutation = list(range(case.d))
    row_rng.shuffle(permutation)
    positions = [[] for _ in range(case.d)]
    coefficients = [[] for _ in range(case.d)]
    rows = []
    for index in range(case.n):
        axis = permutation[index % case.d]
        coefficient = diagonal_coefficient(case, axis, index, row_rng)
        positions[axis].append(index)
        coefficients[axis].append(coefficient)
        rows.append([coefficient * value % modulus for value in matrix[axis]])
    tables = [SparseGCD(values) for values in coefficients]

    def ideal(axis: int, left: int, right: int) -> int:
        first = bisect_left(positions[axis], left)
        last = bisect_right(positions[axis], right)
        if first == last:
            return modulus
        return math.gcd(modulus, tables[axis].query(first, last))

    queries = []
    answers = []
    for index in range(case.q):
        positive = positive_query(answer_rng, index)
        left, right = interval(query_rng, case.n, case.d, index, prefix=case.prefix)
        divisors = [ideal(axis, left, right) for axis in range(case.d)]
        canonical = [divisor * query_rng.randrange(modulus // divisor)
                     for divisor in divisors]
        if not positive:
            candidates = [axis for axis, divisor in enumerate(divisors) if divisor > 1]
            assert candidates
            deep = [axis for axis in candidates
                    if any(divisors[axis] % (prime * prime) == 0
                           for prime, _ in case.factors)]
            axis = query_rng.choice(deep or candidates)
            witness = 1
            for prime, _ in case.factors:
                if divisors[axis] % (prime * prime) == 0:
                    witness = divisors[axis] // prime
                    break
            canonical[axis] = witness
        target = transform(canonical, matrix, modulus)
        queries.append((left, right, target))
        answers.append(positive)
    return rows, queries, answers


def generate(case: Case):
    row_rng = random.Random(case.seed)
    query_rng = random.Random(case.seed + 1)
    answer_rng = random.Random(case.seed + 2)
    if case.mode == "exhaustive":
        return make_exhaustive(case, row_rng, query_rng, answer_rng)
    if case.mode == "local":
        return make_local(case, row_rng, query_rng, answer_rng)
    if case.mode.startswith("coupled"):
        return make_coupled(case, row_rng, query_rng, answer_rng)
    if case.mode == "nonunit":
        return make_nonunit(case, row_rng, query_rng, answer_rng)
    if case.mode == "one-dimensional":
        return make_one_dimensional(case, row_rng, query_rng, answer_rng)
    if case.mode.startswith("diagonal"):
        return make_diagonal(case, row_rng, query_rng, answer_rng)
    raise ValueError(case.mode)


def write_case(case: Case, output: Path) -> dict:
    rows, queries, answers = generate(case)
    input_path = output / f"{case.case_id}.in"
    answer_path = output / f"{case.case_id}.ans"
    with input_path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"{case.n} {case.d} {case.modulus} {case.q}\n")
        for row in rows:
            stream.write(" ".join(map(str, row)) + "\n")
        for left, right, target in queries:
            stream.write(f"{left + 1} {right + 1} " + " ".join(map(str, target)) + "\n")
    with answer_path.open("w", encoding="ascii", newline="\n") as stream:
        stream.writelines("YES\n" if answer else "NO\n" for answer in answers)
    metadata = asdict(case)
    metadata.update({
        "modulus": case.modulus,
        "K": sum(exponent for _, exponent in case.factors),
        "w": len(case.factors),
        "yes": sum(answers),
        "no": len(answers) - sum(answers),
        "input_bytes": input_path.stat().st_size,
        "answer_bytes": answer_path.stat().st_size,
        "input_sha256": sha256(input_path),
        "answer_sha256": sha256(answer_path),
        "oracle": ("complete coefficient closure" if case.mode == "exhaustive"
                   else "constructed positive / independently certified negative"),
    })
    return metadata


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent / "data")
    parser.add_argument("--case", action="append", dest="selected",
                        help="generate only this two-digit case id; may be repeated")
    args = parser.parse_args()
    selected = set(args.selected or [case.case_id for case in CASES])
    unknown = selected - {case.case_id for case in CASES}
    if unknown:
        parser.error(f"unknown case ids: {sorted(unknown)}")
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema": "astra4oi.range-module.data.v1",
        "answer_policy": "labels use the independent seed+2 stream; every NO has a certificate",
        "cases": [write_case(case, args.output) for case in CASES if case.case_id in selected],
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    total = sum(item["input_bytes"] + item["answer_bytes"] for item in manifest["cases"])
    print(f"generated {len(manifest['cases'])} cases, {total} bytes")


if __name__ == "__main__":
    main()
