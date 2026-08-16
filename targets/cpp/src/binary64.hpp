// The binary64 instance of FloatOps.
//
// Specification: lean/CORALean/Arithmetic/Float/Instances/ — by analogy only.
// Lean's instances are Dyadic and ℝ; binary64 has no Lean counterpart because
// it cannot have one. Every property `SoundFloatArithmetic` demands is an
// assumption about this file and the toolchain, listed in ../README.md.
//
// The rounding mode is set once, to FE_UPWARD, and never changed: switching it
// per operation would dominate the run time. The downward operations are
// obtained by negating into the upward one, which is exact because negation is.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cfenv>

#include "float_ops.hpp"

#if defined(__clang__) || defined(_MSC_VER)
#pragma STDC FENV_ACCESS ON
#endif

namespace cora {

template <>
struct FloatOps<double> {
  static double zero() { return 0.0; }
  static double neg(double a) { return -a; }

  static double addUp(double a, double b) { return a + b; }
  static double mulUp(double a, double b) { return a * b; }

  // -(( -a) + (-b)) rounded up is (a + b) rounded down.
  static double addDown(double a, double b) { return -((-a) + (-b)); }
  static double mulDown(double a, double b) { return -((-a) * b); }

  static double minimum(double a, double b) { return a < b ? a : b; }
  static double maximum(double a, double b) { return a > b ? a : b; }

  // Exact: halving only moves the exponent, so the rounding mode does not apply.
  static double half(double a) { return 0.5 * a; }
};

/// Installs round-toward-+infinity for its lifetime. Every call into this
/// library must happen inside one; the results are wrong, not merely imprecise,
/// under any other mode.
class RoundUpGuard {
 public:
  RoundUpGuard() : saved_(std::fegetround()) { std::fesetround(FE_UPWARD); }
  ~RoundUpGuard() { std::fesetround(saved_); }

  RoundUpGuard(const RoundUpGuard&) = delete;
  RoundUpGuard& operator=(const RoundUpGuard&) = delete;

 private:
  int saved_;
};

/// For assertions at the entry points of long-running code.
inline bool roundingIsUp() { return std::fegetround() == FE_UPWARD; }

}  // namespace cora
