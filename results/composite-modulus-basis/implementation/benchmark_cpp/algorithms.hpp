#pragma once

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <deque>
#include <functional>
#include <limits>
#include <numeric>
#include <queue>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace cmbbench {

using Word = std::uint32_t;
using Wide = std::uint64_t;
using SignedWide = __int128_t;
using DoubleWide = __uint128_t;
using Row = std::vector<Word>;

struct Factor { Word p; int k; };
struct Query { int left, right; Row target; };
struct Input {
    int n, d;
    Word modulus;
    std::vector<Row> rows;
    std::vector<Query> queries;
    std::vector<Factor> factors;
};

struct Counters {
    Wide visits = 0, reductions = 0, writes = 0, pops = 0, max_pending = 0;
};

// Products of two residues fit uint64_t for every supported modulus < 2^32.
inline Word mul(Word a, Word b, Word m) { return Wide(a) * b % m; }
inline Word sub(Word a, Word b, Word m) {
    return a >= b ? a - b : Wide(a) + m - b;
}
inline Word signed_residue(SignedWide a, Word m) {
    a %= m;
    if (a < 0) a += m;
    return static_cast<Word>(a);
}

struct Bezout { Wide g; SignedWide s, t; };
inline Bezout bezout(Wide a, Wide b) {
    SignedWide s = 1, t = 0, u = 0, v = 1;
    while (b) {
        Wide q = a / b, remainder = a % b;
        a = b; b = remainder;
        SignedWide ns = s - SignedWide(q) * u, nt = t - SignedWide(q) * v;
        s = u; u = ns; t = v; v = nt;
    }
    return {a, s, t};
}
inline Word inverse(Word a, Word m) {
    auto result = bezout(a, m);
    if (result.g != 1) throw std::logic_error("attempted to invert a nonunit");
    return signed_residue(result.s, m);
}
inline Word prime_power(Factor f) {
    Wide result = 1;
    for (int e = 0; e < f.k; ++e) {
        result *= f.p;
        if (result > std::numeric_limits<Word>::max())
            throw std::invalid_argument("prime power exceeds the 32-bit domain");
    }
    return result;
}
inline bool nonzero(const Row& row, int start = 0) {
    return std::any_of(row.begin() + start, row.end(), [](Word x) { return x != 0; });
}

// Exact reciprocal reduction, never floating point. floor(2^64/m) gives a
// quotient underestimated by at most one for a uint64_t dividend.
class Reducer {
    Word m_, mask_;
    Wide reciprocal_;
    bool power_two_;
public:
    explicit Reducer(Word m) : m_(m), mask_(m - 1),
        reciprocal_(static_cast<Wide>((DoubleWide(1) << 64) / m)),
        power_two_((m & (m - 1)) == 0) {}
    Word mod() const { return m_; }
    bool power_two() const { return power_two_; }
    Word reduce(Wide value) const {
        if (power_two_) return static_cast<Word>(value) & mask_;
        Wide quotient = static_cast<Wide>((DoubleWide(value) * reciprocal_) >> 64);
        Wide remainder = value - quotient * m_;
        return static_cast<Word>(remainder >= m_ ? remainder - m_ : remainder);
    }
    Word multiply(Word a, Word b) const { return reduce(Wide(a) * b); }
    Word subtract(Word a, Word b) const { return sub(a, b, m_); }
    Word unit_inverse(Word a) const {
        if (a == 1) return 1;
        if (!power_two_) return inverse(a, m_);
        if (!(a & 1)) throw std::logic_error("power-of-two inverse needs an odd unit");
        // Every odd a satisfies a*a=1 mod 8. Newton doubles the number of
        // correct bits; uint32_t wraparound is intentional and well-defined.
        Word result = a;
        int exponent = __builtin_ctz(m_);
        for (int bits = 3; bits < exponent; bits *= 2)
            result *= 2U - a * result;
        return result & mask_;
    }
};

// Extended Euclid for a 32-bit unit. Coefficients alternate signs and their
// magnitudes never exceed m, so signed 64-bit intermediates suffice. Keeping
// the remainders at 32 bits also avoids wide division in the hot inverse path.
inline Word inverse32(Word a, Word m) {
    Word r = m, next = a;
    std::int64_t t = 0, u = 1;
    while (next) {
        Word q = r / next, remainder = r - q * next;
        std::int64_t v = t - std::int64_t(q) * u;
        r = next; next = remainder; t = u; u = v;
    }
    if (r != 1) throw std::logic_error("attempted to invert a nonunit");
    return static_cast<Word>(t < 0 ? t + m : t);
}

struct Pivot { int time = 0, level = 0; Row row; };
struct Task { int time, level, start; Row row; };
struct TaskOrder {
    bool operator()(const Task& a, const Task& b) const {
        return a.time != b.time ? a.time < b.time : a.level > b.level;
    }
};

// Readable STL implementation: owning task rows, a priority_queue and full-row
// modular passes. No deliberate slowdown; same algorithm and tie policy as Python.
class BasicTimestamp {
    Word p_, m_;
    int k_, d_;
    Row powers_;
    std::vector<Pivot> slots_;
    Counters* c_;
    int valuation(Word x) const {
        int lo = 0, hi = k_;
        while (hi - lo > 1) {
            int mid = (lo + hi) / 2;
            if (x % powers_[mid] == 0) lo = mid; else hi = mid;
        }
        return lo;
    }
    void subtract(Row& row, const Row& pivot, Word coefficient) {
        for (int j = 0; j < d_; ++j) row[j] = sub(row[j], mul(coefficient, pivot[j], m_), m_);
        ++c_->reductions;
    }
public:
    BasicTimestamp(Factor f, int d, Counters& c) : p_(f.p), m_(prime_power(f)),
        k_(f.k), d_(d), powers_(k_ + 1, 1), slots_(d * k_), c_(&c) {
        for (int e = 1; e <= k_; ++e) powers_[e] = Wide(powers_[e - 1]) * p_;
    }
    void append(const Row& source, int time) {
        Row row(d_);
        for (int j = 0; j < d_; ++j) row[j] = source[j] % m_;
        std::priority_queue<Task, std::vector<Task>, TaskOrder> queue;
        for (int e = 0; e < k_ && nonzero(row); ++e) {
            queue.push({time, e, 0, row});
            if (e + 1 < k_) for (auto& x : row) x = mul(x, p_, m_);
        }
        c_->max_pending = std::max(c_->max_pending, Wide(queue.size()));
        while (!queue.empty()) {
            Task task = queue.top(); queue.pop(); ++c_->pops;
            for (int j = task.start; j < d_; ++j) {
                ++c_->visits;
                if (!task.row[j]) continue;
                int v = valuation(task.row[j]);
                auto& slot = slots_[j * k_ + v];
                if (slot.time == task.time) throw std::logic_error("same-time collision");
                if (slot.time < task.time) {
                    Word inv = inverse(task.row[j] / powers_[v], m_);
                    for (auto& x : task.row) x = mul(x, inv, m_);
                    Pivot old = std::move(slot);
                    slot = {task.time, task.level, std::move(task.row)};
                    ++c_->writes;
                    if (old.time) {
                        subtract(old.row, slot.row, old.row[j] / powers_[v]);
                        if (nonzero(old.row)) queue.push({old.time, old.level, j + 1, std::move(old.row)});
                    }
                    break;
                }
                subtract(task.row, slot.row, task.row[j] / powers_[v]);
            }
            c_->max_pending = std::max(c_->max_pending, Wide(queue.size()));
        }
    }
    bool contains(const Row& target, int left) const {
        Row row(d_);
        for (int j = 0; j < d_; ++j) row[j] = target[j] % m_;
        for (int j = 0; j < d_; ++j) if (row[j]) {
            int v = valuation(row[j]);
            const auto& slot = slots_[j * k_ + v];
            if (slot.time < left) return false;
            Word coefficient = row[j] / powers_[v];
            for (int h = 0; h < d_; ++h) row[h] = sub(row[h], mul(coefficient, slot.row[h], m_), m_);
        }
        return true;
    }
};

// Same task order, with a flat pivot table and k reusable task buffers. A popped
// buffer either finishes or becomes the single displaced successor. No row
// allocation in append; only the nonzero suffix is updated.
class FastTimestamp {
    struct Meta { int time = 0, level = 0, start = 0; };
    Word p_, m_;
    int k_, d_;
    Reducer arithmetic_;
    // Inverses are cached only below 2^16 (at most 256 KiB/component).
    // Very small odd rings use a multiplication table of at most 4 KiB.
    Row powers_, rows_, work_, query_, odd_inverse_, divisibility_limit_, inverse_cache_, products_;
    std::vector<Meta> slots_, tasks_;
    std::vector<int> heap_;
    Counters* c_;
    int unit_count_ = 0, full_since_ = 0;
    bool full_dirty_ = false;
    int valuation(Word x) const {
        if (p_ == 2) return __builtin_ctz(x);
        int lo = 0, hi = k_;
        while (hi - lo > 1) {
            int mid = (lo + hi) / 2;
            if (Word(x * odd_inverse_[mid]) <= divisibility_limit_[mid]) lo = mid; else hi = mid;
        }
        return lo;
    }
    Word quotient(Word x, int v) const {
        // x is exactly divisible by p^v. For odd p, multiplication by its
        // inverse modulo 2^32 recovers the (32-bit) integer quotient.
        return p_ == 2 ? x >> v : x * odd_inverse_[v];
    }
    Word unit_inverse(Word x) {
        if (p_ == 2) return arithmetic_.unit_inverse(x);
        if (x == 1) return 1;
        if (inverse_cache_.empty()) return inverse32(x, m_);
        Word& cached = inverse_cache_[x];
        if (!cached) cached = inverse32(x, m_);
        return cached;
    }
    void eliminate(Word* row, const Word* pivot, Word coefficient, int start) const {
        if (p_ == 2) {
            const Word mask = m_ - 1;
            // Unsigned wraparound followed by a mask is exact modulo 2^k;
            // keeping all lanes at 32 bits lets the compiler vectorize.
            for (int h = start; h < d_; ++h)
                row[h] = (row[h] - coefficient * pivot[h]) & mask;
        } else if (!products_.empty()) {
            const Word* product = products_.data() + coefficient * m_;
            for (int h = start; h < d_; ++h) {
                Word r = row[h] + m_ - product[pivot[h]];
                row[h] = r >= m_ ? r - m_ : r;
            }
        } else {
            for (int h = start; h < d_; ++h)
                row[h] = arithmetic_.subtract(row[h], arithmetic_.multiply(coefficient, pivot[h]));
        }
    }
    bool replace(Word* row, Word* pivot, Word inv, int start, bool occupied) const {
        Word residual = 0;
        if (p_ == 2) {
            const Word mask = m_ - 1;
            if (occupied) {
                for (int h = start; h < d_; ++h) {
                    Word normalized = (row[h] * inv) & mask;
                    row[h] = (pivot[h] - normalized) & mask;
                    residual |= row[h];
                    pivot[h] = normalized;
                }
            } else {
                for (int h = start; h < d_; ++h) pivot[h] = (row[h] * inv) & mask;
            }
        } else if (!products_.empty()) {
            const Word* product = products_.data() + inv * m_;
            if (occupied) {
                for (int h = start; h < d_; ++h) {
                    Word normalized = product[row[h]];
                    Word r = pivot[h] + m_ - normalized;
                    row[h] = r >= m_ ? r - m_ : r;
                    residual |= row[h];
                    pivot[h] = normalized;
                }
            } else {
                for (int h = start; h < d_; ++h) pivot[h] = product[row[h]];
            }
        } else if (occupied) {
            for (int h = start; h < d_; ++h) {
                Word normalized = arithmetic_.multiply(row[h], inv);
                row[h] = arithmetic_.subtract(pivot[h], normalized);
                residual |= row[h];
                pivot[h] = normalized;
            }
        } else {
            for (int h = start; h < d_; ++h) pivot[h] = arithmetic_.multiply(row[h], inv);
        }
        return residual != 0;
    }
    bool before(int a, int b) const {
        return tasks_[a].time != tasks_[b].time ? tasks_[a].time < tasks_[b].time
                                               : tasks_[a].level > tasks_[b].level;
    }
public:
    FastTimestamp(Factor f, int d, Counters& c) : p_(f.p), m_(prime_power(f)),
        k_(f.k), d_(d), arithmetic_(m_), powers_(k_ + 1, 1),
        rows_(std::size_t(d) * k_ * d), work_(k_ * d), query_(d),
        odd_inverse_(k_ + 1, 1), divisibility_limit_(k_ + 1),
        inverse_cache_(p_ != 2 && m_ <= 65536 ? m_ : 0),
        products_(p_ != 2 && m_ <= 32 ? m_ * m_ : 0),
        slots_(d * k_), tasks_(k_), c_(&c) {
        for (int e = 1; e <= k_; ++e) powers_[e] = Wide(powers_[e - 1]) * p_;
        if (p_ != 2) for (int e = 0; e <= k_; ++e) {
            Word x = powers_[e], inv = x;
            for (int bits = 3; bits < 32; bits *= 2) inv *= 2U - x * inv;
            odd_inverse_[e] = inv;
            divisibility_limit_[e] = std::numeric_limits<Word>::max() / x;
        }
        if (!products_.empty()) for (Word a = 0; a < m_; ++a)
            for (Word b = 0; b < m_; ++b) products_[a * m_ + b] = a * b % m_;
        heap_.reserve(k_);
    }
    void append(const Row& source, int time) {
        heap_.clear();
        for (int j = 0; j < d_; ++j) work_[j] = arithmetic_.reduce(source[j]);
        for (int e = 0; e < k_; ++e) {
            Word* row = work_.data() + e * d_;
            if (!std::any_of(row, row + d_, [](Word x) { return x; })) break;
            tasks_[e] = {time, e, 0}; heap_.push_back(e);
            if (e + 1 < k_) for (int j = 0; j < d_; ++j)
                work_[(e + 1) * d_ + j] = arithmetic_.multiply(row[j], p_);
        }
        // Equal timestamps and increasing levels already form a max heap.
        c_->max_pending = std::max(c_->max_pending, Wide(heap_.size()));
        while (!heap_.empty()) {
            int id = heap_[0]; ++c_->pops;
            bool successor = false;
            Meta task = tasks_[id];
            Word* row = work_.data() + id * d_;
            for (int j = task.start; j < d_; ++j) {
                ++c_->visits;
                if (!row[j]) continue;
                int v = valuation(row[j]), index = j * k_ + v;
                Meta old = slots_[index];
                Word* pivot = rows_.data() + std::size_t(index) * d_;
                if (old.time == task.time) throw std::logic_error("same-time collision");
                if (old.time < task.time) {
                    Word inv = unit_inverse(quotient(row[j], v));
                    bool has_residual = replace(row, pivot, inv, j + 1, old.time != 0);
                    pivot[j] = powers_[v];
                    row[j] = 0;
                    if (v == 0) {
                        unit_count_ += old.time == 0;
                        full_dirty_ = true;
                    }
                    slots_[index] = {task.time, task.level, 0}; ++c_->writes;
                    if (old.time) ++c_->reductions;
                    if (has_residual) {
                        tasks_[id] = {old.time, old.level, j + 1};
                        successor = true;
                    }
                    break;
                }
                Word coefficient = quotient(row[j], v);
                eliminate(row, pivot, coefficient, j + 1);
                row[j] = 0;
                ++c_->reductions;
            }
            // A displaced successor has a strictly older timestamp. Replace
            // the root and sift down once, instead of pop_heap + push_heap.
            if (!successor) {
                heap_[0] = heap_.back();
                heap_.pop_back();
            }
            if (!heap_.empty()) {
                int root = heap_[0], hole = 0, size = static_cast<int>(heap_.size());
                for (int child = 1; child < size; child = 2 * hole + 1) {
                    if (child + 1 < size && before(heap_[child], heap_[child + 1])) ++child;
                    if (!before(root, heap_[child])) break;
                    heap_[hole] = heap_[child];
                    hole = child;
                }
                heap_[hole] = root;
            }
        }
    }
    bool contains(const Row& target, int left) {
        // A triangular set of unit pivots is a basis of the whole module.
        // Their minimum timestamp certifies every suffix starting before it.
        // Cache once between writes; deficient modules never pay for a scan.
        if (unit_count_ == d_) {
            if (full_dirty_) {
                full_since_ = slots_[0].time;
                for (int j = 1; j < d_; ++j)
                    full_since_ = std::min(full_since_, slots_[j * k_].time);
                full_dirty_ = false;
            }
            if (left <= full_since_) return true;
        }
        for (int j = 0; j < d_; ++j) query_[j] = arithmetic_.reduce(target[j]);
        for (int j = 0; j < d_; ++j) if (query_[j]) {
            int v = valuation(query_[j]), index = j * k_ + v;
            if (slots_[index].time < left) return false;
            const Word* pivot = rows_.data() + std::size_t(index) * d_;
            Word coefficient = quotient(query_[j], v);
            eliminate(query_.data(), pivot, coefficient, j + 1);
        }
        return true;
    }
};

// Historical project prototype: explicitly propagate p*pivot after every write.
// This is an ablation, not a claim to implement an externally published method.
class ClosureTimestamp {
    Word p_, m_;
    int k_, d_;
    Row powers_;
    std::vector<Pivot> slots_;
    Counters* c_;
    int valuation(Word x) const {
        int v = 0;
        while (x % p_ == 0) { x /= p_; ++v; }
        return v;
    }
public:
    ClosureTimestamp(Factor f, int d, Counters& c) : p_(f.p), m_(prime_power(f)),
        k_(f.k), d_(d), powers_(k_ + 1, 1), slots_(d * k_), c_(&c) {
        for (int e = 1; e <= k_; ++e) powers_[e] = Wide(powers_[e - 1]) * p_;
    }
    void append(const Row& source, int time) {
        Row initial = source;
        for (auto& x : initial) x %= m_;
        std::deque<std::pair<Row, int>> queue;
        queue.emplace_back(std::move(initial), time);
        while (!queue.empty()) {
            c_->max_pending = std::max(c_->max_pending, Wide(queue.size()));
            auto item = std::move(queue.front()); queue.pop_front(); ++c_->pops;
            Row row = std::move(item.first);
            int tag = item.second;
            for (int j = 0; j < d_; ++j) {
                ++c_->visits;
                if (!row[j]) continue;
                int v = valuation(row[j]);
                auto& slot = slots_[j * k_ + v];
                if (slot.time < tag) {
                    Word inv = inverse(row[j] / powers_[v], m_);
                    for (auto& x : row) x = mul(x, inv, m_);
                    Pivot old = std::move(slot);
                    slot = {tag, 0, std::move(row)}; ++c_->writes;
                    Row multiple = slot.row;
                    for (auto& x : multiple) x = mul(x, p_, m_);
                    if (nonzero(multiple)) queue.emplace_back(std::move(multiple), tag);
                    if (!old.time) break;
                    row = std::move(old.row); tag = old.time;
                }
                Word coefficient = row[j] / powers_[v];
                for (int h = j; h < d_; ++h) row[h] = sub(row[h], mul(coefficient, slot.row[h], m_), m_);
                ++c_->reductions;
            }
        }
    }
    bool contains(const Row& target, int left) const {
        Row row = target;
        for (auto& x : row) x %= m_;
        for (int j = 0; j < d_; ++j) if (row[j]) {
            int v = valuation(row[j]);
            const auto& slot = slots_[j * k_ + v];
            if (slot.time < left) return false;
            Word coefficient = row[j] / powers_[v];
            for (int h = j; h < d_; ++h) row[h] = sub(row[h], mul(coefficient, slot.row[h], m_), m_);
        }
        return true;
    }
};

// Factorization-free saturated triangular module generators. This is a local
// Howell-style implementation, not a canonical/full fast Howell library.
// Bezout updates preserve the generated module; annihilator residuals supply
// the closure needed for complete forward membership reduction.
class HowellBasis {
    Word m_;
    int d_, units_ = 0;
    Reducer arithmetic_;
    std::vector<Row> pivots_;
public:
    HowellBasis(Word m, int d) : m_(m), d_(d), arithmetic_(m), pivots_(d) {}
    bool full() const { return units_ == d_; }
    void insert(Row input) {
        if (full()) return;
        std::vector<Row> pending;
        pending.push_back(std::move(input));
        while (!pending.empty()) {
            Row row = std::move(pending.back()); pending.pop_back();
            for (int j = 0; j < d_; ++j) {
                if (!row[j]) continue;
                Row& pivot = pivots_[j];
                if (pivot.empty()) {
                    if (arithmetic_.power_two() && (row[j] & 1)) {
                        Word inv = arithmetic_.unit_inverse(row[j]);
                        for (int h = j; h < d_; ++h) row[h] = arithmetic_.multiply(row[h], inv);
                        pivot = std::move(row); ++units_;
                        break;
                    }
                    auto b = bezout(row[j], m_);
                    Row annihilator(d_);
                    Word multiplier = m_ / b.g;
                    for (int h = j; h < d_; ++h)
                        annihilator[h] = arithmetic_.multiply(row[h], multiplier);
                    // Treat m*e_j as an implicit zero row in a unimodular gcd
                    // step. The annihilator of the ORIGINAL row must survive.
                    for (int h = j; h < d_; ++h) row[h] = signed_residue(b.s * row[h], m_);
                    pivot = std::move(row);
                    if (pivot[j] == 1) ++units_;
                    if (nonzero(annihilator, j + 1)) pending.push_back(std::move(annihilator));
                    break;
                }
                if (row[j] % pivot[j] == 0) {
                    Word coefficient = row[j] / pivot[j];
                    for (int h = j; h < d_; ++h)
                        row[h] = arithmetic_.subtract(row[h], arithmetic_.multiply(coefficient, pivot[h]));
                } else {
                    if (arithmetic_.power_two() && (row[j] & 1)) {
                        // The incoming row is a unit pivot. Normalize it with
                        // the same Newton primitive as timestamp-fast, and keep
                        // the displaced old row as its exact residual.
                        Word inv = arithmetic_.unit_inverse(row[j]);
                        for (int h = j; h < d_; ++h) row[h] = arithmetic_.multiply(row[h], inv);
                        row.swap(pivot); ++units_;
                        Word coefficient = row[j];
                        for (int h = j; h < d_; ++h)
                            row[h] = arithmetic_.subtract(row[h], arithmetic_.multiply(coefficient, pivot[h]));
                        continue;
                    }
                    Word a = pivot[j], b = row[j];
                    auto coefficients = bezout(a, b);
                    Row annihilator(d_);
                    Word multiplier = m_ / coefficients.g;
                    for (int h = j; h < d_; ++h) {
                        Word old = pivot[h], incoming = row[h];
                        pivot[h] = signed_residue(coefficients.s * old + coefficients.t * incoming, m_);
                        row[h] = signed_residue(-SignedWide(b / coefficients.g) * old
                                                + SignedWide(a / coefficients.g) * incoming, m_);
                        annihilator[h] = arithmetic_.multiply(pivot[h], multiplier);
                    }
                    if (a != 1 && pivot[j] == 1) ++units_;
                    if (nonzero(annihilator, j + 1)) pending.push_back(std::move(annihilator));
                }
            }
        }
    }
    void merge(const HowellBasis& other) {
        for (const auto& row : other.pivots_) {
            if (full()) break;
            if (!row.empty()) insert(row);
        }
    }
    bool contains(Row target) const {
        if (full()) return true;
        for (int j = 0; j < d_; ++j) if (target[j]) {
            const auto& pivot = pivots_[j];
            if (pivot.empty() || target[j] % pivot[j]) return false;
            Word coefficient = target[j] / pivot[j];
            for (int h = j; h < d_; ++h)
                target[h] = arithmetic_.subtract(target[h], arithmetic_.multiply(coefficient, pivot[h]));
        }
        return true;
    }
};

inline std::vector<std::vector<int>> buckets(const Input& in) {
    std::vector<std::vector<int>> result(in.n + 1);
    for (int i = 0; i < static_cast<int>(in.queries.size()); ++i) result[in.queries[i].right].push_back(i);
    return result;
}

template<class Basis>
std::vector<std::uint8_t> timestamp_solve(const Input& in, Counters& counters) {
    std::vector<Basis> components;
    components.reserve(in.factors.size());
    for (auto f : in.factors) components.emplace_back(f, in.d, counters);
    auto by_right = buckets(in);
    std::vector<std::uint8_t> answers(in.queries.size());
    for (int r = 1; r <= in.n; ++r) {
        for (auto& basis : components) basis.append(in.rows[r - 1], r);
        for (int i : by_right[r]) {
            bool answer = true;
            for (auto& basis : components) if (!basis.contains(in.queries[i].target, in.queries[i].left)) {
                answer = false; break;
            }
            answers[i] = answer;
        }
    }
    return answers;
}

inline std::vector<std::uint8_t> howell_solve(const Input& in, const std::string& method) {
    std::vector<std::uint8_t> answers(in.queries.size());
    if (method == "howell-rebuild") {
        for (std::size_t i = 0; i < in.queries.size(); ++i) {
            const auto& q = in.queries[i];
            HowellBasis basis(in.modulus, in.d);
            for (int j = q.left - 1; j < q.right && !basis.full(); ++j) basis.insert(in.rows[j]);
            answers[i] = basis.contains(q.target);
        }
    } else if (method == "howell-segment") {
        int size = 1;
        while (size < in.n) size *= 2;
        std::vector<HowellBasis> tree;
        tree.reserve(2 * size);
        for (int i = 0; i < 2 * size; ++i) tree.emplace_back(in.modulus, in.d);
        for (int i = 0; i < in.n; ++i) tree[size + i].insert(in.rows[i]);
        for (int i = size - 1; i; --i) { tree[i].merge(tree[2 * i]); tree[i].merge(tree[2 * i + 1]); }
        for (std::size_t i = 0; i < in.queries.size(); ++i) {
            const auto& q = in.queries[i];
            HowellBasis basis(in.modulus, in.d);
            int l = size + q.left - 1, r = size + q.right;
            while (l < r && !basis.full()) {
                if (l & 1) basis.merge(tree[l++]);
                if (r & 1) basis.merge(tree[--r]);
                l /= 2; r /= 2;
            }
            answers[i] = basis.contains(q.target);
        }
    } else {
        std::vector<std::vector<HowellBasis>> table(1);
        table[0].reserve(in.n);
        for (const auto& row : in.rows) {
            table[0].emplace_back(in.modulus, in.d); table[0].back().insert(row);
        }
        for (int level = 1; (Wide(1) << level) <= static_cast<Wide>(in.n); ++level) {
            int length = 1 << level, half = length / 2;
            table.emplace_back(); table[level].reserve(in.n - length + 1);
            for (int i = 0; i + length <= in.n; ++i) {
                table[level].push_back(table[level - 1][i]);
                table[level].back().merge(table[level - 1][i + half]);
            }
        }
        for (std::size_t i = 0; i < in.queries.size(); ++i) {
            const auto& q = in.queries[i];
            int level = 31 - __builtin_clz(static_cast<unsigned>(q.right - q.left + 1));
            HowellBasis basis = table[level][q.left - 1];
            basis.merge(table[level][q.right - (1 << level)]);
            answers[i] = basis.contains(q.target);
        }
    }
    return answers;
}

// The established field-only timestamp method, independently implemented without
// power levels or a task queue, and given the same fast modular arithmetic.
inline std::vector<std::uint8_t> field_solve(const Input& in) {
    if (in.factors.size() != 1 || in.factors[0].k != 1)
        throw std::domain_error("field-timestamp requires a prime modulus");
    Reducer arithmetic(in.modulus);
    std::vector<Row> pivots(in.d, Row(in.d));
    std::vector<int> times(in.d);
    auto by_right = buckets(in);
    std::vector<std::uint8_t> answers(in.queries.size());
    for (int r = 1; r <= in.n; ++r) {
        Row row = in.rows[r - 1]; int time = r;
        for (int j = 0; j < in.d; ++j) if (row[j]) {
            if (times[j] < time) {
                Word inv = arithmetic.unit_inverse(row[j]);
                for (int h = j; h < in.d; ++h) row[h] = arithmetic.multiply(row[h], inv);
                std::swap(row, pivots[j]); std::swap(time, times[j]);
                if (!time) break;
            }
            Word coefficient = row[j];
            for (int h = j; h < in.d; ++h)
                row[h] = arithmetic.subtract(row[h], arithmetic.multiply(coefficient, pivots[j][h]));
        }
        for (int i : by_right[r]) {
            Row target = in.queries[i].target; bool answer = true;
            for (int j = 0; j < in.d; ++j) if (target[j]) {
                if (times[j] < in.queries[i].left) { answer = false; break; }
                Word coefficient = target[j];
                for (int h = j; h < in.d; ++h)
                    target[h] = arithmetic.subtract(target[h], arithmetic.multiply(coefficient, pivots[j][h]));
            }
            answers[i] = answer;
        }
    }
    return answers;
}

inline std::vector<std::uint8_t> xor_solve(const Input& in) {
    if (in.modulus != 2 || in.d > 64) throw std::domain_error("xor-packed requires m=2 and d<=64");
    auto pack = [&](const Row& row) {
        Wide result = 0;
        for (int j = 0; j < in.d; ++j) result |= Wide(row[j]) << j;
        return result;
    };
    std::vector<Wide> pivots(in.d);
    std::vector<int> times(in.d);
    auto by_right = buckets(in);
    std::vector<std::uint8_t> answers(in.queries.size());
    for (int r = 1; r <= in.n; ++r) {
        Wide row = pack(in.rows[r - 1]); int time = r;
        while (row) {
            int j = __builtin_ctzll(row);
            if (!times[j]) { pivots[j] = row; times[j] = time; break; }
            if (times[j] < time) { std::swap(row, pivots[j]); std::swap(time, times[j]); }
            row ^= pivots[j];
        }
        for (int i : by_right[r]) {
            Wide target = pack(in.queries[i].target); bool answer = true;
            while (target) {
                int j = __builtin_ctzll(target);
                if (times[j] < in.queries[i].left) { answer = false; break; }
                target ^= pivots[j];
            }
            answers[i] = answer;
        }
    }
    return answers;
}

inline std::vector<std::uint8_t> solve(const Input& in, const std::string& name, Counters& c) {
    if (name == "timestamp-basic") return timestamp_solve<BasicTimestamp>(in, c);
    if (name == "timestamp-fast") return timestamp_solve<FastTimestamp>(in, c);
    if (name == "closure-prototype") return timestamp_solve<ClosureTimestamp>(in, c);
    if (name == "howell-rebuild" || name == "howell-segment" || name == "howell-sparse") return howell_solve(in, name);
    if (name == "field-timestamp") return field_solve(in);
    if (name == "xor-packed") return xor_solve(in);
    throw std::invalid_argument("unknown algorithm: " + name);
}

} // namespace cmbbench
