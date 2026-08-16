// Interval operations enclose what they claim to.
//
// Specification: lean/src/CORALean/Arithmetic/Float/ContSet/Interval/Theorems.lean
//
// The shape of every soundness test here: take a point the input denotes, apply
// the operation exactly, and check the result still denotes it. Lean states the
// same thing as `⊆` over all points at once.
//
// Test data is exactly representable — small integers — so the reference point
// is computed without rounding and the checks need no tolerance. Rounding is
// exercised in float_ops.cpp, where it is the subject rather than a nuisance.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#include "binary64.hpp"
#include "check.hpp"
#include "interval.hpp"

using namespace cora;
using namespace cora::test;

namespace {

/// An interval with integer bounds, and a point inside it, both exact.
Interval<double> randomBox(Rng& rng, std::size_t n) {
  Interval<double> I{Vec<double>(n), Vec<double>(n)};
  for (std::size_t i = 0; i < n; ++i) {
    const double a = rng.smallInt(100);
    const double b = rng.smallInt(100);
    I.inf[i] = a < b ? a : b;
    I.sup[i] = a < b ? b : a;
  }
  return I;
}

Vec<double> samplePoint(Rng& rng, const Interval<double>& I) {
  Vec<double> x(I.dim());
  for (std::size_t i = 0; i < I.dim(); ++i)
    x[i] = static_cast<double>(rng.intIn(static_cast<std::int64_t>(I.inf[i]),
                                         static_cast<std::int64_t>(I.sup[i])));
  return x;
}

bool contains(const Interval<double>& I, const Vec<double>& x) {
  for (std::size_t i = 0; i < I.dim(); ++i)
    if (!(I.inf[i] <= x[i] && x[i] <= I.sup[i])) return false;
  return true;
}

}  // namespace

int main() {
  RoundUpGuard guard;
  Rng rng(0xC0FFEE);

  // symmetric: the box [-r, r].
  for (int t = 0; t < 200; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 5));
    Vec<double> r(n);
    for (std::size_t i = 0; i < n; ++i) r[i] = rng.anyDouble(1e2) + 1e2;
    const Interval<double> S = Interval<double>::symmetric(r);
    bool ok = true, zero = true;
    for (std::size_t i = 0; i < n; ++i) {
      ok = ok && S.inf[i] == -r[i] && S.sup[i] == r[i];
      zero = zero && S.inf[i] <= 0.0 && 0.0 <= S.sup[i];
    }
    check("symmetric bounds", ok);
    check("symmetric holds 0", zero);
  }

  // residual: whatever [lo, hi] holds, stored + residual holds too.
  for (int t = 0; t < 500; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 5));
    const Interval<double> B = randomBox(rng, n);
    const Vec<double> stored = samplePoint(rng, B);
    const Vec<double> v = samplePoint(rng, B);
    const Interval<double> R = Interval<double>::residual(B.inf, B.sup, stored);

    Vec<double> diff(n);
    for (std::size_t i = 0; i < n; ++i) diff[i] = v[i] - stored[i];
    check("v - stored in residual", contains(R, diff));
  }

  // plus: x in I1 and y in I2 gives x + y in I1.plus(I2).
  for (int t = 0; t < 500; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 5));
    const Interval<double> I1 = randomBox(rng, n);
    const Interval<double> I2 = randomBox(rng, n);
    const Vec<double> x = samplePoint(rng, I1);
    const Vec<double> y = samplePoint(rng, I2);

    Vec<double> sum(n);
    for (std::size_t i = 0; i < n; ++i) sum[i] = x[i] + y[i];
    check("plus encloses", contains(I1.plus(I2), sum));
  }

  // mtimes: x in I gives M*x in mtimes(M, I). M has negative entries, since the
  // sign is what minimum/maximum are there to absorb.
  for (int t = 0; t < 500; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 4));
    const std::size_t m = static_cast<std::size_t>(rng.intIn(1, 4));
    const Interval<double> I = randomBox(rng, n);
    const Vec<double> x = samplePoint(rng, I);

    Mat<double> M(m, n);
    for (std::size_t i = 0; i < m; ++i)
      for (std::size_t k = 0; k < n; ++k) M(i, k) = rng.smallInt(50);

    Vec<double> Mx(m, 0.0);
    for (std::size_t i = 0; i < m; ++i)
      for (std::size_t k = 0; k < n; ++k) Mx[i] += M(i, k) * x[k];

    check("mtimes encloses", contains(Interval<double>::mtimes(M, I), Mx));
  }

  // inf <= sup is the invariant every operation must preserve, and the one that
  // silently breaks if a rounding direction is flipped.
  for (int t = 0; t < 500; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 5));
    Interval<double> I1{Vec<double>(n), Vec<double>(n)};
    Interval<double> I2{Vec<double>(n), Vec<double>(n)};
    for (std::size_t i = 0; i < n; ++i) {
      const double a = rng.anyDouble(1e3), b = rng.anyDouble(1e3);
      I1.inf[i] = a < b ? a : b;
      I1.sup[i] = a < b ? b : a;
      const double c = rng.anyDouble(1e3), d = rng.anyDouble(1e3);
      I2.inf[i] = c < d ? c : d;
      I2.sup[i] = c < d ? d : c;
    }
    Mat<double> M(n, n);
    for (std::size_t i = 0; i < n; ++i)
      for (std::size_t k = 0; k < n; ++k) M(i, k) = rng.anyDouble(10.0);

    const Interval<double> P = I1.plus(I2);
    const Interval<double> T = Interval<double>::mtimes(M, I1);
    bool okP = true, okT = true;
    for (std::size_t i = 0; i < n; ++i) {
      okP = okP && P.inf[i] <= P.sup[i];
      okT = okT && T.inf[i] <= T.sup[i];
    }
    check("plus keeps inf<=sup", okP);
    check("mtimes keeps inf<=sup", okT);
  }

  return report("interval");
}
