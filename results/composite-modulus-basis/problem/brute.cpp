#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using u64 = std::uint64_t;
using Row = std::vector<int>;

static u64 encode(const Row& row, int modulus) {
    u64 result = 0;
    for (int value : row) result = result * modulus + value;
    return result;
}

static Row decode(u64 state, int dimension, int modulus) {
    Row result(dimension);
    for (int column = dimension - 1; column >= 0; --column) {
        result[column] = int(state % modulus);
        state /= modulus;
    }
    return result;
}

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int n, dimension, modulus, query_count;
    if (!(std::cin >> n >> dimension >> modulus >> query_count)) return 0;
    std::vector<Row> vectors(n, Row(dimension));
    for (Row& row : vectors) for (int& value : row) std::cin >> value;

    u64 states = 1;
    for (int column = 0; column < dimension; ++column) {
        states *= modulus;
        if (states > 2000000) {
            std::cerr << "brute.cpp requires m^d <= 2,000,000\n";
            return 2;
        }
    }

    while (query_count--) {
        int left, right;
        std::cin >> left >> right;
        Row target(dimension);
        for (int& value : target) std::cin >> value;
        if (right - left + 1 > 14) {
            std::cerr << "brute.cpp requires interval length <= 14\n";
            return 2;
        }

        std::vector<unsigned char> reachable(states, false), next(states, false);
        reachable[0] = true;
        for (int index = left - 1; index < right; ++index) {
            next = reachable;
            for (u64 state = 0; state < states; ++state) {
                if (!reachable[state]) continue;
                Row value = decode(state, dimension, modulus);
                for (int coefficient = 1; coefficient < modulus; ++coefficient) {
                    Row sum(dimension);
                    for (int column = 0; column < dimension; ++column) {
                        sum[column] = int((std::int64_t(value[column])
                                           + std::int64_t(coefficient) * vectors[index][column])
                                          % modulus);
                    }
                    next[encode(sum, modulus)] = true;
                }
            }
            reachable.swap(next);
        }
        std::cout << (reachable[encode(target, modulus)] ? "YES\n" : "NO\n");
    }
    return 0;
}
