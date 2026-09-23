#include "../../implementation/benchmark_cpp/algorithms.hpp"

#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using namespace cmbbench;

struct PrefixQuery {
    int index;
    Row target;
};

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int n, dimension, query_count;
    Word modulus;
    if (!(std::cin >> n >> dimension >> modulus >> query_count)) return 0;
    std::vector<Row> rows(n, Row(dimension));
    for (Row& row : rows) for (Word& value : row) std::cin >> value;
    std::vector<std::vector<PrefixQuery>> by_right(n + 1);
    for (int index = 0; index < query_count; ++index) {
        int left, right;
        std::cin >> left >> right;
        if (left != 1) {
            std::cerr << "prefix-howell requires l=1\n";
            return 64;
        }
        Row target(dimension);
        for (Word& value : target) std::cin >> value;
        by_right[right].push_back({index, std::move(target)});
    }
    HowellBasis basis(modulus, dimension);
    std::vector<std::uint8_t> answers(query_count);
    for (int right = 1; right <= n; ++right) {
        basis.insert(rows[right - 1]);
        for (const PrefixQuery& query : by_right[right]) {
            answers[query.index] = basis.contains(query.target);
        }
    }
    for (std::uint8_t answer : answers) std::cout << (answer ? "YES\n" : "NO\n");
}
