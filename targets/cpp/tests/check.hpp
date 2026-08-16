// Minimal test harness: a counter, a check, and a deterministic generator.
//
// No framework on purpose — a test here should be readable next to the Lean
// theorem it stands for, and a dependency would obscure that.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cstdint>
#include <cstdio>

namespace cora::test {

inline int checks = 0;
inline int failures = 0;

inline void check(const char* what, bool ok) {
  ++checks;
  if (!ok) {
    ++failures;
    std::printf("  FAIL  %s\n", what);
  }
}

/// Call once at the end of main and return its value.
inline int report(const char* suite) {
  std::printf("%-14s %3d checks, %d failed\n", suite, checks, failures);
  return failures == 0 ? 0 : 1;
}

/// xorshift64*, seeded fixed so a failure reproduces. Not <random>, whose
/// distributions are not specified to give the same values across libraries.
class Rng {
 public:
  explicit Rng(std::uint64_t seed = 0x9E3779B97F4A7C15ULL) : s_(seed) {}

  std::uint64_t next() {
    s_ ^= s_ >> 12;
    s_ ^= s_ << 25;
    s_ ^= s_ >> 27;
    return s_ * 0x2545F4914F6CDD1DULL;
  }

  std::int64_t intIn(std::int64_t lo, std::int64_t hi) {
    return lo + static_cast<std::int64_t>(next() % static_cast<std::uint64_t>(hi - lo + 1));
  }

  /// A small integer, so sums and products of these stay exact in binary64.
  double smallInt(int bound = 1000) { return static_cast<double>(intIn(-bound, bound)); }

  /// A coefficient in [-1, 1] that is a multiple of 1/1024, so scaling a
  /// smallInt by it stays exact.
  double unitCoeff() { return static_cast<double>(intIn(-1024, 1024)) / 1024.0; }

  /// A generic double, with 53 random mantissa bits — for rounding tests, where
  /// exactly representable operands would hide the very thing under test.
  double anyDouble(double scale = 1.0) {
    const double u = static_cast<double>(next() >> 11) / 9007199254740992.0;
    return (u * 2.0 - 1.0) * scale;
  }

 private:
  std::uint64_t s_;
};

}  // namespace cora::test
