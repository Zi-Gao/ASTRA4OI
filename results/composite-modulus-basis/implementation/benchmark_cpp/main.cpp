#include "algorithms.hpp"

#include <array>
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <sys/resource.h>

using namespace cmbbench;

// The same buffered judge I/O is used for every algorithm.
class FastInput {
    std::array<unsigned char, 1 << 16> buffer_{};
    std::size_t position_ = 0, length_ = 0;
    int current_ = ' ';
    int get() {
        if (position_ == length_) {
            length_ = std::fread(buffer_.data(), 1, buffer_.size(), stdin);
            position_ = 0;
            if (!length_) return EOF;
        }
        return buffer_[position_++];
    }
public:
    bool next(std::int64_t& value) {
        while (current_ != EOF && current_ <= ' ') current_ = get();
        if (current_ == EOF) return false;
        bool negative = current_ == '-';
        if (negative || current_ == '+') current_ = get();
        if (current_ < '0' || current_ > '9') throw std::invalid_argument("expected an integer");
        Wide magnitude = 0, limit = Wide(std::numeric_limits<std::int64_t>::max()) + negative;
        while (current_ >= '0' && current_ <= '9') {
            unsigned digit = static_cast<unsigned>(current_ - '0');
            if (magnitude > (limit - digit) / 10) throw std::invalid_argument("integer outside signed 64-bit range");
            magnitude = magnitude * 10 + digit;
            current_ = get();
        }
        if (current_ != EOF && current_ > ' ') throw std::invalid_argument("invalid integer suffix");
        if (negative && magnitude == (Wide(1) << 63)) value = std::numeric_limits<std::int64_t>::min();
        else value = negative ? -static_cast<std::int64_t>(magnitude) : static_cast<std::int64_t>(magnitude);
        return true;
    }
};

static bool prime(Word p) {
    if (p < 2) return false;
    for (Wide d = 2; d * d <= p; d = d == 2 ? 3 : d + 2) if (p % d == 0) return false;
    return true;
}

static std::vector<Factor> parse_factors(std::string text, Word modulus) {
    std::vector<Factor> result;
    std::istringstream parts(text);
    std::string part;
    Wide product = 1;
    while (std::getline(parts, part, ',')) {
        auto colon = part.find(':');
        if (colon == std::string::npos) throw std::invalid_argument("use p:k,p:k for factors");
        Wide p = std::stoull(part.substr(0, colon));
        int k = std::stoi(part.substr(colon + 1));
        if (p > std::numeric_limits<Word>::max() || !prime(static_cast<Word>(p)) || k < 1 || k > 31)
            throw std::invalid_argument("invalid prime power");
        for (auto f : result) if (f.p == p) throw std::invalid_argument("duplicate prime factor");
        Factor factor{static_cast<Word>(p), k};
        Wide power = prime_power(factor);
        if (product > modulus / power) throw std::invalid_argument("factor product exceeds modulus");
        product *= power; result.push_back(factor);
    }
    if (product != modulus) throw std::invalid_argument("factor product does not equal modulus");
    return result;
}

static Wide peak_rss() {
    rusage usage{};
    if (getrusage(RUSAGE_SELF, &usage)) return 0;
#ifdef __APPLE__
    return usage.ru_maxrss;
#else
    return Wide(usage.ru_maxrss) * 1024;
#endif
}

int main(int argc, char** argv) {
    try {
        std::string algorithm = "timestamp-fast", factors;
        for (int i = 1; i < argc; ++i) {
            std::string option = argv[i];
            if (option == "--algorithm" && i + 1 < argc) algorithm = argv[++i];
            else if (option == "--factors" && i + 1 < argc) factors = argv[++i];
            else throw std::invalid_argument("usage: bench --algorithm NAME --factors p:k,p:k < input");
        }
        using Clock = std::chrono::steady_clock;
        auto start = Clock::now();
        FastInput scanner;
        Input input{}; std::int64_t n, d, modulus, q_count;
        if (!scanner.next(n) || !scanner.next(d) || !scanner.next(modulus) || !scanner.next(q_count)
            || n < 1 || n > 10000000 || d < 1 || d > 256
            || modulus < 2 || modulus > std::numeric_limits<Word>::max()
            || q_count < 0 || q_count > std::numeric_limits<int>::max())
            throw std::invalid_argument("expected n>=1, 1<=d<=256, 2<=m<2^32, q>=0");
        input.n = static_cast<int>(n); input.d = static_cast<int>(d);
        int query_count = static_cast<int>(q_count);
        input.modulus = static_cast<Word>(modulus);
        if (!factors.empty()) input.factors = parse_factors(factors, input.modulus);
        else if (algorithm.rfind("howell-", 0) != 0 && algorithm != "xor-packed")
            throw std::invalid_argument("this algorithm requires --factors");
        auto read_row = [&]() {
            Row row(input.d);
            for (auto& x : row) {
                std::int64_t value;
                if (!scanner.next(value)) throw std::invalid_argument("missing row entries");
                if (value >= 0 && static_cast<Wide>(value) < input.modulus) x = static_cast<Word>(value);
                else {
                    value %= static_cast<std::int64_t>(input.modulus);
                    if (value < 0) value += input.modulus;
                    x = static_cast<Word>(value);
                }
            }
            return row;
        };
        input.rows.reserve(input.n);
        for (int i = 0; i < input.n; ++i) input.rows.push_back(read_row());
        input.queries.reserve(query_count);
        for (int i = 0; i < query_count; ++i) {
            std::int64_t l, r;
            if (!scanner.next(l) || !scanner.next(r) || l < 1 || l > r || r > input.n)
                throw std::invalid_argument("invalid interval");
            input.queries.push_back({static_cast<int>(l), static_cast<int>(r), read_row()});
        }
        std::int64_t extra;
        if (scanner.next(extra)) throw std::invalid_argument("trailing input");
        auto parsed = Clock::now();
        Counters counters;
        auto answers = solve(input, algorithm, counters);
        auto solved = Clock::now();
        Wide hash = 14695981039346656037ULL, yes = 0;
        std::string output;
        output.reserve(4 * answers.size());
        for (auto answer : answers) {
            yes += answer;
            hash = (hash ^ answer) * 1099511628211ULL;
            output += answer ? "YES\n" : "NO\n";
        }
        if (std::fwrite(output.data(), 1, output.size(), stdout) != output.size() || std::fflush(stdout))
            throw std::runtime_error("failed to write answers");
        auto completed = Clock::now();
        auto seconds = [](auto a, auto b) { return std::chrono::duration<double>(b - a).count(); };
        std::cerr << std::setprecision(12)
            << "{\"algorithm\":\"" << algorithm << "\",\"parse_seconds\":" << seconds(start, parsed)
            << ",\"solve_seconds\":" << seconds(parsed, solved)
            << ",\"program_seconds\":" << seconds(start, completed)
            << ",\"peak_rss_bytes\":" << peak_rss()
            << ",\"yes\":" << yes << ",\"queries\":" << answers.size()
            << ",\"answer_hash\":\"" << hash << "\",\"visits\":" << counters.visits
            << ",\"reductions\":" << counters.reductions << ",\"writes\":" << counters.writes
            << ",\"pops\":" << counters.pops << ",\"max_pending\":" << counters.max_pending << "}\n";
        return 0;
    } catch (const std::domain_error& error) {
        std::cerr << error.what() << '\n'; return 64;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n'; return 1;
    }
}
