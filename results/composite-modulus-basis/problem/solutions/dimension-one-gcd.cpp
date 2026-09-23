#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using i64 = std::int64_t;

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int n, dimension, query_count;
    i64 modulus;
    if (!(std::cin >> n >> dimension >> modulus >> query_count)) return 0;
    if (dimension != 1) {
        std::cerr << "dimension-one-gcd requires d=1\n";
        return 64;
    }
    int size = 1;
    while (size < n) size *= 2;
    std::vector<i64> tree(2 * size, 0);
    for (int index = 0; index < n; ++index) std::cin >> tree[size + index];
    for (int index = size - 1; index > 0; --index) {
        tree[index] = std::gcd(tree[2 * index], tree[2 * index + 1]);
    }
    auto range_gcd = [&](int left, int right) {
        i64 result = modulus;
        for (left += size - 1, right += size; left < right; left /= 2, right /= 2) {
            if (left & 1) result = std::gcd(result, tree[left++]);
            if (right & 1) result = std::gcd(result, tree[--right]);
        }
        return result;
    };
    while (query_count--) {
        int left, right;
        i64 target;
        std::cin >> left >> right >> target;
        std::cout << (target % range_gcd(left, right) == 0 ? "YES\n" : "NO\n");
    }
}
