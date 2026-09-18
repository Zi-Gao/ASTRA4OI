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
                ++checks;
            }
            checks += 3;
        }
    }
    std::cout << "PASS exact reciprocal/mask arithmetic: " << checks << " comparisons\n";
}
