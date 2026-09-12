"""Priority-ordered insertion: only k incoming power rows, no closure branching."""

import heapq
from experiment import PrimePowerBasis, check_sequence, generated_span
from itertools import product
import random


class FastPrimePowerBasis(PrimePowerBasis):
    def insert(self, vector, timestamp):
        queue = []
        row = [a % self.mod for a in vector]
        for level in range(self.k):
            if not any(row):
                break
            heapq.heappush(queue, (-timestamp, level, 0, row))
            row = [(a * self.p) % self.mod for a in row]
        while queue:
            minus_tag, level, start, row = heapq.heappop(queue)
            tag = -minus_tag
            self.tasks += 1
            for j in range(start, self.d):
                if not row[j]:
                    continue
                v = self.valuation(row[j])
                old = self.table[j][v]
                assert old is None or old[0] != tag, ("same tag collision", timestamp, tag, level, j, v, old)
                if old is None or tag > old[0]:
                    unit = pow(row[j] // self.powers[v], -1, self.mod)
                    self.table[j][v] = (tag, [a * unit % self.mod for a in row], level)
                    self.updates += 1
                    if old is None:
                        break
                    old_tag, old_row, old_level = old
                    factor = old_row[j] // self.powers[v]
                    residual = [(a - factor * b) % self.mod for a, b in zip(old_row, self.table[j][v][1])]
                    self.reductions += 1
                    if any(residual):
                        heapq.heappush(queue, (-old_tag, old_level, j + 1, residual))
                    break
                factor = row[j] // self.powers[v]
                row = [(a - factor * b) % self.mod for a, b in zip(row, old[1])]
                self.reductions += 1


def main():
    rng = random.Random(11926)
    sequences = checks = 0
    for p, k, d, length in [(2, 2, 2, 3), (2, 3, 1, 4)]:
        u = list(product(range(p**k), repeat=d))
        for seq in product(u, repeat=length):
            b = FastPrimePowerBasis(p, k, d)
            for r, a in enumerate(seq, 1):
                b.insert(a, r)
                for l in range(1, r + 1):
                    span = generated_span(seq[l-1:r], p**k, d)
                    for x in u:
                        assert b.contains(x,l) == (x in span), (p,k,seq,l,r,x,b.table)
                        checks += 1
            sequences += 1
        print("exhaustive passed", p,k,d,length,flush=True)
    for it in range(10000):
        p = rng.choice([2,3,5,7]); k=rng.randrange(1,9); d=rng.randrange(1,10); mod=p**k
        hidden=[[rng.randrange(mod) for _ in range(d)] for _ in range(rng.randrange(1,d+1))]
        b=FastPrimePowerBasis(p,k,d); c=PrimePowerBasis(p,k,d)
        for r in range(1,2*d+3):
            co=[rng.randrange(mod)*p**rng.randrange(k)%mod for _ in hidden]
            a=tuple(sum(z*x[j] for z,x in zip(co,hidden))%mod for j in range(d))
            b.insert(a,r); c.insert(a,r)
            bt=[[s[0] if s else -1 for s in col] for col in b.table]
            ct=[[s[0] if s else -1 for s in col] for col in c.table]
            assert bt==ct, (p,k,d,it,r,bt,ct)
        sequences += 1
    print(f"PASS: {sequences} sequences; {checks} brute-force membership checks; 10000 structured random comparisons",flush=True)


if __name__ == "__main__":
    main()
