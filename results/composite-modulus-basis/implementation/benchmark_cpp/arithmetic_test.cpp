#include "algorithms.hpp"
#include <iostream>
#include <random>

int main() {
    using namespace cmbbench;
    std::mt19937_64 rng(20260917);
    Wide checks = 0;
    for (Word m : {2U, 4U, 72U, 59049U, 65536U, 998244353U, 2147483648U, 4294967291U, 4294967295U}) {
        Reducer reducer(m);
        for (Wide value : {Wide(0), Wide(1), Wide(m - 1), Wide(m), Wide(m) + 1,
                           Wide(m - 1) * (m - 1), std::numeric_limits<Wide>::max()}) {
            if (reducer.reduce(value) != value % m) return 1;
            ++checks;
        }
        for (int i = 0; i < 100000; ++i) {
            Wide value = rng();
            Word a = rng() % m, b = rng() % m;
            if (reducer.reduce(value) != value % m || reducer.multiply(a, b) != Wide(a) * b % m
                || reducer.subtract(a, b) != (Wide(a) + m - b) % m) return 2;
            if (std::gcd(a, m) == 1) {
                if (reducer.multiply(a, inverse(a, m)) != 1) return 3;
                if (Wide(a) * reducer.unit_inverse(a) % m != 1) return 4;
                if (Wide(a) * inverse32(a, m) % m != 1) return 5;
                checks += 2;
            }
            checks += 3;
        }
    }
    // Exercise every valuation at large odd prime powers, full-module cache
    // invalidation, missing pivots, and the maximum supported dimension.
    for (Factor f : {Factor{2, 31}, {3, 3}, {5, 2}, {31, 1}, {3, 20}, {5, 13}, {65521, 2}, {4294967291U, 1}}) {
        Word m = prime_power(f);
        for (int d : {1, 7, 32, 256}) {
            Counters bc, fc;
            BasicTimestamp basic(f, d, bc);
            FastTimestamp fast(f, d, fc);
            int n = d == 256 ? 8 : d + f.k + 5;
            Word scale = 1;
            for (int time = 1; time <= n; ++time) {
                Row row(d);
                for (auto& x : row) x = Wide(rng() % m) * scale % m;
                if (time <= d) {
                    std::fill(row.begin(), row.end(), 0);
                    row[time - 1] = 1;
                }
                basic.append(row, time); fast.append(row, time);
                if (bc.visits != fc.visits || bc.reductions != fc.reductions ||
                    bc.writes != fc.writes || bc.pops != fc.pops || bc.max_pending != fc.max_pending) return 6;
                for (int left : {1, std::max(1, time - d + 1), time}) {
                    for (int target = 0; target < 3; ++target) {
                        Row query(d, 0);
                        if (target == 1) query = row;
                        if (target == 2) for (auto& x : query) x = rng() % m;
                        if (basic.contains(query, left) != fast.contains(query, left)) return 7;
                        ++checks;
                    }
                }
                scale = Wide(scale) * f.p % m;
                if (!scale) scale = 1;
            }
        }
    }
    std::cout << "PASS arithmetic and timestamp boundary regression: " << checks << " comparisons\n";
}
