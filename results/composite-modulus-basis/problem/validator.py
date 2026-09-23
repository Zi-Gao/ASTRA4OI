#!/usr/bin/env python3
"""Strict validator for the OI problem package."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


MAX_N = 100_000
MAX_Q = 100_000
MAX_D = 30
MAX_MODULUS = 2_000_000_000
MAX_K = 8
MAX_COMPONENTS = 4
MAX_WORK = 150_000_000


class ValidationError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def factorize(value: int) -> list[tuple[int, int]]:
    factors = []
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        if remaining % divisor == 0:
            exponent = 0
            while remaining % divisor == 0:
                remaining //= divisor
                exponent += 1
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors.append((remaining, 1))
    return factors


def parse_integer_tokens(path: Path) -> list[int]:
    try:
        raw = path.read_bytes()
        text = raw.decode("ascii")
    except (OSError, UnicodeDecodeError) as error:
        raise ValidationError(f"cannot read an ASCII input: {error}") from error
    pieces = text.split()
    require(pieces, "input is empty")
    values = []
    for index, piece in enumerate(pieces, 1):
        try:
            values.append(int(piece))
        except ValueError as error:
            raise ValidationError(f"token {index} is not an integer") from error
    return values


def validate(path: Path, subtask: str) -> dict[str, int | bool]:
    values = parse_integer_tokens(path)
    require(len(values) >= 4, "missing n, d, m, q")
    n, dimension, modulus, query_count = values[:4]
    require(1 <= n <= MAX_N, f"n must be in [1, {MAX_N}]")
    require(1 <= query_count <= MAX_Q, f"q must be in [1, {MAX_Q}]")
    require(1 <= dimension <= MAX_D, f"d must be in [1, {MAX_D}]")
    require(2 <= modulus <= MAX_MODULUS,
            f"m must be in [2, {MAX_MODULUS}]")

    factors = factorize(modulus)
    exponent_sum = sum(exponent for _, exponent in factors)
    component_count = len(factors)
    require(exponent_sum <= MAX_K, f"K={exponent_sum} exceeds {MAX_K}")
    require(component_count <= MAX_COMPONENTS,
            f"w={component_count} exceeds {MAX_COMPONENTS}")
    work = (n * exponent_sum + query_count * component_count) * dimension * dimension
    require(work <= MAX_WORK, f"work budget {work} exceeds {MAX_WORK}")

    expected = 4 + n * dimension + query_count * (dimension + 2)
    require(len(values) == expected,
            f"expected {expected} integers, found {len(values)}")
    cursor = 4
    for row in range(1, n + 1):
        for column in range(1, dimension + 1):
            value = values[cursor]
            cursor += 1
            require(0 <= value < modulus,
                    f"a[{row}][{column}]={value} is outside [0,m)")

    all_prefix = True
    for query in range(1, query_count + 1):
        left, right = values[cursor:cursor + 2]
        cursor += 2
        require(1 <= left <= right <= n,
                f"query {query} has invalid interval [{left},{right}]")
        all_prefix &= left == 1
        for column in range(1, dimension + 1):
            value = values[cursor]
            cursor += 1
            require(0 <= value < modulus,
                    f"query {query}, coordinate {column} is outside [0,m)")

    if subtask == "small":
        require(n <= 80 and query_count <= 120 and dimension <= 4 and modulus <= 1000,
                "small-subtask limits are not satisfied")
    elif subtask == "dimension-one":
        require(dimension == 1, "dimension-one subtask requires d=1")
    elif subtask == "prime":
        require(factors == [(modulus, 1)], "prime subtask requires a prime modulus")
    elif subtask == "squarefree":
        require(all(exponent == 1 for _, exponent in factors),
                "squarefree subtask requires every prime exponent to be one")
    elif subtask == "prefix":
        require(all_prefix, "prefix subtask requires l=1 for every query")
    elif subtask != "full":
        raise ValidationError(f"unknown subtask {subtask!r}")

    return {
        "n": n,
        "d": dimension,
        "m": modulus,
        "q": query_count,
        "K": exponent_sum,
        "w": component_count,
        "work": work,
        "squarefree": all(exponent == 1 for _, exponent in factors),
        "prime": factors == [(modulus, 1)],
        "prefix": all_prefix,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--subtask", default="full",
                        choices=("small", "dimension-one", "prime", "squarefree", "prefix", "full"))
    args = parser.parse_args()
    try:
        summary = validate(args.input, args.subtask)
    except ValidationError as error:
        print(f"invalid: {error}", file=sys.stderr)
        raise SystemExit(1)
    print("valid " + " ".join(f"{key}={value}" for key, value in summary.items()))


if __name__ == "__main__":
    main()
