#include <algorithm>
#include <cstdint>
#include <iostream>
#include <queue>
#include <stdexcept>
#include <utility>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;
using Row = std::vector<u32>;

struct Factor {
    u32 prime;
    int exponent;
};

static std::vector<Factor> factorize(u32 value) {
    std::vector<Factor> result;
    u32 remaining = value;
    for (u32 p = 2; u64(p) * p <= remaining; p = (p == 2 ? 3 : p + 2)) {
        if (remaining % p != 0) continue;
        int exponent = 0;
        do {
            remaining /= p;
            ++exponent;
        } while (remaining % p == 0);
        result.push_back({p, exponent});
    }
    if (remaining > 1) result.push_back({remaining, 1});
    return result;
}

static u32 subtract_mod(u32 a, u32 b, u32 modulus) {
    return a >= b ? a - b : u32(u64(a) + modulus - b);
}

static u32 multiply_mod(u32 a, u32 b, u32 modulus) {
    return u32(u64(a) * b % modulus);
}

static u32 inverse_mod(u32 value, u32 modulus) {
    // value is always a unit modulo modulus.
    std::int64_t old_r = modulus, r = value;
    std::int64_t old_t = 0, t = 1;
    while (r != 0) {
        const std::int64_t quotient = old_r / r;
        const std::int64_t next_r = old_r - quotient * r;
        const std::int64_t next_t = old_t - quotient * t;
        old_r = r;
        r = next_r;
        old_t = t;
        t = next_t;
    }
    if (old_r != 1) throw std::logic_error("inverse of a non-unit");
    old_t %= modulus;
    if (old_t < 0) old_t += modulus;
    return u32(old_t);
}

class PrimePowerBasis {
    struct Pivot {
        int timestamp = 0;
        int level = 0;
        Row row;
    };

    struct Task {
        int timestamp;
        int level;
        int start_column;
        Row row;
    };

    struct OlderFirst {
        bool operator()(const Task& lhs, const Task& rhs) const {
            if (lhs.timestamp != rhs.timestamp) return lhs.timestamp < rhs.timestamp;
            return lhs.level > rhs.level;
        }
    };

    u32 prime_;
    u32 modulus_;
    int exponent_;
    int dimension_;
    std::vector<u32> powers_;
    std::vector<Pivot> table_;

    int valuation(u32 value) const {
        int low = 0, high = exponent_;
        while (high - low > 1) {
            const int middle = (low + high) / 2;
            if (value % powers_[middle] == 0) {
                low = middle;
            } else {
                high = middle;
            }
        }
        return low;
    }

    bool nonzero(const Row& row, int start = 0) const {
        return std::any_of(row.begin() + start, row.end(), [](u32 value) {
            return value != 0;
        });
    }

    void eliminate(Row& row, const Row& pivot, u32 coefficient, int start) const {
        for (int column = start; column < dimension_; ++column) {
            row[column] = subtract_mod(
                row[column], multiply_mod(coefficient, pivot[column], modulus_), modulus_);
        }
    }

public:
    PrimePowerBasis(Factor factor, int dimension)
        : prime_(factor.prime), modulus_(1), exponent_(factor.exponent),
          dimension_(dimension), powers_(exponent_ + 1, 1),
          table_(std::size_t(dimension_) * exponent_) {
        for (int level = 1; level <= exponent_; ++level) {
            modulus_ = u32(u64(modulus_) * prime_);
            powers_[level] = modulus_;
        }
    }

    void append(const Row& source, int timestamp) {
        Row row(dimension_);
        for (int column = 0; column < dimension_; ++column) {
            row[column] = source[column] % modulus_;
        }

        std::priority_queue<Task, std::vector<Task>, OlderFirst> pending;
        for (int level = 0; level < exponent_ && nonzero(row); ++level) {
            pending.push({timestamp, level, 0, row});
            if (level + 1 < exponent_) {
                for (u32& value : row) value = multiply_mod(value, prime_, modulus_);
            }
        }

        while (!pending.empty()) {
            Task task = pending.top();
            pending.pop();

            for (int column = task.start_column; column < dimension_; ++column) {
                if (task.row[column] == 0) continue;
                const int order = valuation(task.row[column]);
                Pivot& slot = table_[std::size_t(column) * exponent_ + order];

                // The timestamped-basis invariant proves that this cannot occur.
                if (slot.timestamp == task.timestamp) {
                    throw std::logic_error("same-timestamp pivot collision");
                }

                if (slot.timestamp < task.timestamp) {
                    const u32 unit = task.row[column] / powers_[order];
                    const u32 inverse = inverse_mod(unit, modulus_);
                    for (int next = column; next < dimension_; ++next) {
                        task.row[next] = multiply_mod(task.row[next], inverse, modulus_);
                    }

                    Pivot displaced = std::move(slot);
                    slot.timestamp = task.timestamp;
                    slot.level = task.level;
                    slot.row = std::move(task.row);

                    if (displaced.timestamp != 0) {
                        const u32 coefficient = displaced.row[column] / powers_[order];
                        eliminate(displaced.row, slot.row, coefficient, column);
                        if (nonzero(displaced.row, column + 1)) {
                            pending.push({displaced.timestamp, displaced.level,
                                          column + 1, std::move(displaced.row)});
                        }
                    }
                    break;
                }

                const u32 coefficient = task.row[column] / powers_[order];
                eliminate(task.row, slot.row, coefficient, column);
            }
        }
    }

    bool contains(const Row& target, int left_endpoint) const {
        Row row(dimension_);
        for (int column = 0; column < dimension_; ++column) {
            row[column] = target[column] % modulus_;
        }

        for (int column = 0; column < dimension_; ++column) {
            if (row[column] == 0) continue;
            const int order = valuation(row[column]);
            const Pivot& pivot = table_[std::size_t(column) * exponent_ + order];
            if (pivot.timestamp < left_endpoint) return false;
            const u32 coefficient = row[column] / powers_[order];
            eliminate(row, pivot.row, coefficient, column);
        }
        return true;
    }
};

struct Query {
    int index;
    int left;
    Row target;
};

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int n, dimension, query_count;
    u32 modulus;
    if (!(std::cin >> n >> dimension >> modulus >> query_count)) return 0;

    std::vector<Row> vectors(n, Row(dimension));
    for (Row& row : vectors) {
        for (u32& value : row) std::cin >> value;
    }

    std::vector<std::vector<Query>> by_right(n + 1);
    for (int index = 0; index < query_count; ++index) {
        int left, right;
        std::cin >> left >> right;
        Row target(dimension);
        for (u32& value : target) std::cin >> value;
        by_right[right].push_back({index, left, std::move(target)});
    }

    std::vector<PrimePowerBasis> components;
    for (Factor factor : factorize(modulus)) {
        components.emplace_back(factor, dimension);
    }

    std::vector<unsigned char> answers(query_count, false);
    for (int right = 1; right <= n; ++right) {
        for (PrimePowerBasis& basis : components) basis.append(vectors[right - 1], right);
        for (const Query& query : by_right[right]) {
            bool answer = true;
            for (const PrimePowerBasis& basis : components) {
                if (!basis.contains(query.target, query.left)) {
                    answer = false;
                    break;
                }
            }
            answers[query.index] = answer;
        }
    }

    for (unsigned char answer : answers) {
        std::cout << (answer ? "YES\n" : "NO\n");
    }
    return 0;
}
