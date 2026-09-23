#pragma once

#include "../../implementation/benchmark_cpp/algorithms.hpp"

#include <cstdint>
#include <exception>
#include <iostream>
#include <limits>
#include <vector>

#ifndef RANGE_MODULE_ALGORITHM
#error "define RANGE_MODULE_ALGORITHM before including runner.hpp"
#endif

namespace range_module_runner {

using namespace cmbbench;

static std::vector<Factor> factorize(Word modulus) {
    std::vector<Factor> result;
    Word remaining = modulus;
    for (Word prime = 2; Wide(prime) * prime <= remaining;
         prime = (prime == 2 ? 3 : prime + 2)) {
        if (remaining % prime != 0) continue;
        int exponent = 0;
        do {
            remaining /= prime;
            ++exponent;
        } while (remaining % prime == 0);
        result.push_back({prime, exponent});
    }
    if (remaining > 1) result.push_back({remaining, 1});
    return result;
}

static int run() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    try {
        Input input{};
        int query_count;
        std::uint64_t modulus;
        if (!(std::cin >> input.n >> input.d >> modulus >> query_count)) return 0;
        if (modulus > std::numeric_limits<Word>::max()) {
            throw std::invalid_argument("modulus does not fit uint32_t");
        }
        input.modulus = static_cast<Word>(modulus);
        input.factors = factorize(input.modulus);
        input.rows.assign(input.n, Row(input.d));
        for (Row& row : input.rows) {
            for (Word& value : row) std::cin >> value;
        }
        input.queries.reserve(query_count);
        for (int index = 0; index < query_count; ++index) {
            Query query;
            std::cin >> query.left >> query.right;
            query.target.resize(input.d);
            for (Word& value : query.target) std::cin >> value;
            input.queries.push_back(std::move(query));
        }
        Counters counters;
        const auto answers = solve(input, RANGE_MODULE_ALGORITHM, counters);
        for (std::uint8_t answer : answers) {
            std::cout << (answer ? "YES\n" : "NO\n");
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 64;
    }
}

}  // namespace range_module_runner

int main() {
    return range_module_runner::run();
}
