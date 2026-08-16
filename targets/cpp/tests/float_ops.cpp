// The FloatOps axioms, as property tests.
//
// Specification: lean/src/CORALean/Arithmetic/Float/SoundFloatArithmetic.lean
//
// That file states what a scalar must satisfy for the whole layer to be sound.
// Lean discharges it for Dyadic and ℝ; binary64 cannot be an instance, so these
// checks are what stands in for that proof. Adding a new FloatOps
// specialization means running this file against it.
//
// The reference is the round-to-nearest result. It provably lies between the
// two directed roundings — it is one of the neighbours of the exact value — so
// the checks below need no exact arithmetic and carry no tolerance.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#include <cfenv>
#include <cmath>

#include "binary64.hpp"
#include "check.hpp"
#include "float_ops.hpp"

using namespace cora;
using namespace cora::test;
using FO = FloatOps<double>;

namespace {

/// Round-to-nearest for the duration of a reference computation.
struct NearestScope {
  int saved;
  NearestScope() : saved(std::fegetround()) { std::fesetround(FE_TONEAREST); }
  ~NearestScope() { std::fesetround(saved); }
};

double rnAdd(double a, double b) {
  NearestScope s;
  return a + b;
}

double rnMul(double a, double b) {
  NearestScope s;
  return a * b;
}

/// True when a*b is not exactly representable, via TwoProduct: p + err is the
/// exact product and err is representable, so this holds in any rounding mode.
bool mulIsInexact(double a, double b) {
  const double p = rnMul(a, b);
  return std::fma(a, b, -p) != 0.0;
}

}  // namespace

int main() {
  RoundUpGuard guard;
  check("rounding mode is up", roundingIsUp());

  Rng rng;

  // add_le_addUp and addDown_le_add.
  for (int i = 0; i < 2000; ++i) {
    const double a = rng.anyDouble(1e3);
    const double b = rng.anyDouble(1e3);
    const double lo = FO::addDown(a, b);
    const double hi = FO::addUp(a, b);
    const double rn = rnAdd(a, b);

    check("addDown <= addUp", lo <= hi);
    check("addDown <= a+b", lo <= rn);
    check("a+b <= addUp", rn <= hi);
    // Inexact means the two directions must actually differ; equal bounds here
    // would mean a rounding mode that never took effect.
    if (rnAdd(lo, -hi) != 0.0) check("addUp within 1 ulp", std::nextafter(lo, hi) == hi);
  }

  // mul_le_mulUp and mulDown_le_mul.
  for (int i = 0; i < 2000; ++i) {
    const double a = rng.anyDouble(1e3);
    const double b = rng.anyDouble(1e3);
    const double lo = FO::mulDown(a, b);
    const double hi = FO::mulUp(a, b);
    const double rn = rnMul(a, b);

    check("mulDown <= mulUp", lo <= hi);
    check("mulDown <= a*b", lo <= rn);
    check("a*b <= mulUp", rn <= hi);
    if (mulIsInexact(a, b)) check("inexact mul straddles", lo < hi);
  }

  // The operations Lean assumes exact.
  for (int i = 0; i < 2000; ++i) {
    const double a = rng.anyDouble(1e3);
    const double b = rng.anyDouble(1e3);

    check("toReal_neg", FO::neg(a) == -a);
    check("toReal_minimum", FO::minimum(a, b) == (a < b ? a : b));
    check("toReal_maximum", FO::maximum(a, b) == (a > b ? a : b));
    check("toReal_half", FO::half(a) == a / 2.0);
    check("absolute", absolute<double>(a) == std::fabs(a));
  }

  // Exactly representable operands must round to themselves in both directions;
  // a mode leaking into an exact operation would show up here.
  for (int i = 0; i < 1000; ++i) {
    const double a = rng.smallInt();
    const double b = rng.smallInt();
    check("exact add agrees", FO::addDown(a, b) == FO::addUp(a, b));
    check("exact mul agrees", FO::mulDown(a, b) == FO::mulUp(a, b));
  }

  // sub_le_subUp and subDown_le_sub, which Lean derives rather than assumes.
  for (int i = 0; i < 1000; ++i) {
    const double a = rng.anyDouble(1e3);
    const double b = rng.anyDouble(1e3);
    const double rn = rnAdd(a, -b);
    check("subDown <= a-b", subDown<double>(a, b) <= rn);
    check("a-b <= subUp", rn <= subUp<double>(a, b));
  }

  // sum_le_sumUp and sumDown_le_sum. The reference sums in the same order, so
  // this tests the rounding rather than the bracketing.
  for (int trial = 0; trial < 500; ++trial) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 12));
    std::vector<double> v(n);
    for (std::size_t i = 0; i < n; ++i) v[i] = rng.anyDouble(1e2);
    const auto at = [&](std::size_t i) { return v[i]; };

    double rn = 0.0;
    {
      NearestScope s;
      for (std::size_t i = n; i-- > 0;) rn = v[i] + rn;
    }
    check("sumDown <= sum", sumDown<double>(n, at) <= rn);
    check("sum <= sumUp", rn <= sumUp<double>(n, at));
  }

  // radius bounds each row's sum of absolute values, which is the one property
  // every use of it relies on.
  for (int trial = 0; trial < 500; ++trial) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 4));
    const std::size_t h = static_cast<std::size_t>(rng.intIn(1, 8));
    Mat<double> G(n, h);
    for (std::size_t i = 0; i < n; ++i)
      for (std::size_t j = 0; j < h; ++j) G(i, j) = rng.anyDouble(1e2);

    const Vec<double> r = radius<double>(G);
    for (std::size_t i = 0; i < n; ++i) {
      double exact = 0.0;
      {
        NearestScope s;
        for (std::size_t j = h; j-- > 0;) exact = std::fabs(G(i, j)) + exact;
      }
      check("radius bounds row", r[i] >= exact);
      check("radius is nonneg", r[i] >= 0.0);
    }
  }

  return report("float_ops");
}
