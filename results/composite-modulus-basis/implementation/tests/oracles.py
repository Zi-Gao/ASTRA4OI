"""Test-only integer-lattice oracle; no prime factorization or timestamp logic.

For row generators A, membership modulo m is integer-lattice membership in
L = span_Z(A, m*I).  Elementary unimodular row operations triangularize these
generators.  Forward integer substitution decides membership, and the product
of the positive pivots is [Z^d : L], so the module has m^d / index elements.

This is an independent reference algorithm, not a fast range-query solver.
"""

from math import prod


def bezout(a: int, b: int) -> tuple[int, int, int]:
    """Return positive g and s,t satisfying s*a + t*b = g = gcd(a,b)."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


class LatticeOracle:
    def __init__(self, vectors, modulus: int, dimension: int):
        self.modulus, self.dimension = modulus, dimension
        rows = [[a % modulus for a in row] for row in vectors]
        rows.extend([
            [modulus if i == j else 0 for j in range(dimension)]
            for i in range(dimension)
        ])
        for column in range(dimension):
            def bounded_tail(row):
                # The untouched rows m*e_j for j > column are still present.
                # Subtracting their integer multiples is unimodular and keeps
                # later coordinates bounded.  Never apply this to those
                # identity rows themselves (their current coordinate is zero,
                # so the loop below skips them).
                return [a if j <= column else a % modulus for j, a in enumerate(row)]

            # m*I makes the lattice full rank, so a pivot always exists.
            index = min(
                (i for i in range(column, len(rows)) if rows[i][column]),
                key=lambda i: abs(rows[i][column]),
            )
            rows[column], rows[index] = rows[index], rows[column]
            for i in range(column + 1, len(rows)):
                a, b = rows[column][column], rows[i][column]
                if not b:
                    continue
                if b % a == 0:
                    q = b // a
                    rows[i] = bounded_tail([y - q * x for x, y in zip(rows[column], rows[i])])
                else:
                    g, s, t = bezout(a, b)
                    pivot, other = rows[column], rows[i]
                    # [[s,t],[-b/g,a/g]] has determinant 1.
                    rows[column] = bounded_tail([s * x + t * y for x, y in zip(pivot, other)])
                    rows[i] = bounded_tail([-(b // g) * x + (a // g) * y for x, y in zip(pivot, other)])
            if rows[column][column] < 0:
                rows[column] = [-x for x in rows[column]]
            # Keep earlier rows small without changing the lattice.
            for i in range(column):
                q = rows[i][column] // rows[column][column]
                rows[i] = bounded_tail([x - q * y for x, y in zip(rows[i], rows[column])])
        self.rows = rows[:dimension]
        assert all(not any(row) for row in rows[dimension:])
        index = prod(self.rows[j][j] for j in range(dimension))
        self.span_size, remainder = divmod(modulus**dimension, index)
        assert remainder == 0

    def contains(self, target) -> bool:
        residual = [a % self.modulus for a in target]
        for j, pivot in enumerate(self.rows):
            q, remainder = divmod(residual[j], pivot[j])
            if remainder:
                return False
            residual = [x - q * y for x, y in zip(residual, pivot)]
        return not any(residual)
