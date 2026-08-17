// Zonotope operations keep the set they had.
//
// Specification: lean/src/CORALean/Arithmetic/Float/ContSet/Zonotope/Theorems.lean
//
// Two kinds of test here, and the second is the interesting one.
//
// The first samples a point the zonotope denotes and checks the result still
// denotes it. Deciding membership in a zonotope means solving for coefficients,
// so these check membership in the interval hull instead — necessary, not
// sufficient, but enough to catch a transcription error.
//
// The second checks the key lemma of each `_outer` proof directly. Those
// lemmas are all of the form "this radius covers what that part can
// contribute", which is a comparison of two numbers, so the test is exact and
// as strong as the proof step it mirrors.
//
// Test data is exactly representable — integer centres and generators,
// coefficients a multiple of 1/1024 — so every reference value below is
// computed without rounding.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#include <cmath>

#include "binary64.hpp"
#include "check.hpp"
#include "zonotope.hpp"

using namespace cora;
using namespace cora::test;

namespace {

constexpr int kBound = 100;

Zonotope<double> randomZonotope(Rng& rng, std::size_t n, std::size_t h) {
  Zonotope<double> Z{Vec<double>(n), Mat<double>(n, h), Interval<double>{Vec<double>(n), Vec<double>(n)}};
  for (std::size_t i = 0; i < n; ++i) {
    Z.c[i] = rng.smallInt(kBound);
    for (std::size_t j = 0; j < h; ++j) Z.G(i, j) = rng.smallInt(kBound);
    const double a = rng.smallInt(kBound), b = rng.smallInt(kBound);
    Z.E.inf[i] = a < b ? a : b;
    Z.E.sup[i] = a < b ? b : a;
  }
  return Z;
}

Vec<double> sampleCoeffs(Rng& rng, std::size_t h) {
  Vec<double> beta(h);
  for (std::size_t j = 0; j < h; ++j) beta[j] = rng.unitCoeff();
  return beta;
}

Vec<double> sampleError(Rng& rng, const Interval<double>& E) {
  Vec<double> e(E.dim());
  for (std::size_t i = 0; i < E.dim(); ++i)
    e[i] = static_cast<double>(rng.intIn(static_cast<std::int64_t>(E.inf[i]),
                                         static_cast<std::int64_t>(E.sup[i])));
  return e;
}

/// c + G*beta + e, exact for the data above.
Vec<double> buildPoint(const Zonotope<double>& Z, const Vec<double>& beta, const Vec<double>& e) {
  Vec<double> p(Z.dim());
  for (std::size_t i = 0; i < Z.dim(); ++i) {
    double acc = 0.0;
    for (std::size_t j = 0; j < Z.numGenerators(); ++j) acc += Z.G(i, j) * beta[j];
    p[i] = Z.c[i] + acc + e[i];
  }
  return p;
}

bool contains(const Interval<double>& I, const Vec<double>& x) {
  for (std::size_t i = 0; i < I.dim(); ++i)
    if (!(I.inf[i] <= x[i] && x[i] <= I.sup[i])) return false;
  return true;
}

Split randomSplit(Rng& rng, std::size_t h) {
  Split part;
  for (std::size_t j = 0; j < h; ++j) {
    if (rng.intIn(0, 1) == 0)
      part.left.push_back(j);
    else
      part.right.push_back(j);
  }
  return part;
}

}  // namespace

int main() {
  RoundUpGuard guard;
  Rng rng(0x5EED);

  for (int t = 0; t < 800; ++t) {
    const std::size_t n = static_cast<std::size_t>(rng.intIn(1, 4));
    const std::size_t h = static_cast<std::size_t>(rng.intIn(1, 6));
    const Zonotope<double> Z = randomZonotope(rng, n, h);
    const Vec<double> beta = sampleCoeffs(rng, h);
    const Vec<double> e = sampleError(rng, Z.E);
    const Vec<double> p = buildPoint(Z, beta, e);

    // interval_outer.
    check("interval encloses", contains(Z.interval(), p));

    // absorbError_outer: the point survives, and the generator count grows by n.
    const Zonotope<double> A = Z.absorbError();
    check("absorbError count", A.numGenerators() == h + n);
    check("absorbError encloses", contains(A.interval(), p));

    // The lemma behind it, read off the block absorbError actually produced:
    // column h + i is the generator it spends on coordinate i.
    bool errOk = true;
    for (std::size_t i = 0; i < n; ++i) {
      const double mid = (Z.E.inf[i] + Z.E.sup[i]) / 2.0;
      errOk = errOk && std::fabs(e[i] - mid) <= A.G(i, h + i);
    }
    check("errorRadius covers box", errOk);

    // plus_outer: generators concatenate, so the count is h + k.
    const std::size_t k = static_cast<std::size_t>(rng.intIn(1, 6));
    const Zonotope<double> Z2 = randomZonotope(rng, n, k);
    const Vec<double> beta2 = sampleCoeffs(rng, k);
    const Vec<double> e2 = sampleError(rng, Z2.E);
    const Vec<double> p2 = buildPoint(Z2, beta2, e2);
    const Zonotope<double> P = Z.plus(Z2);
    Vec<double> psum(n);
    for (std::size_t i = 0; i < n; ++i) psum[i] = p[i] + p2[i];
    check("plus count", P.numGenerators() == h + k);
    check("plus encloses", contains(P.interval(), psum));

    // mtimes_outer: the count is untouched, the rounding paid into the box.
    Mat<double> M(n, n);
    for (std::size_t i = 0; i < n; ++i)
      for (std::size_t l = 0; l < n; ++l) M(i, l) = rng.smallInt(20);
    Vec<double> Mp(n, 0.0);
    for (std::size_t i = 0; i < n; ++i)
      for (std::size_t l = 0; l < n; ++l) Mp[i] += M(i, l) * p[l];
    const Zonotope<double> T = Zonotope<double>::mtimes(M, Z);
    check("mtimes count", T.numGenerators() == h);
    check("mtimes encloses", contains(T.interval(), Mp));

    // reduce_outer, and the lemma behind it: the diagonal block covers what the
    // dropped generators can contribute.
    const Split part = randomSplit(rng, h);
    check("split is a partition", part.isValid(h));
    const std::size_t q = part.left.size();
    const Zonotope<double> R = Z.reduce(part);
    check("reduce count", R.numGenerators() == q + n);
    check("reduce encloses", contains(R.interval(), p));

    // reduceAndAbsorb costs q + n, not q + n + n: the two blocks merge.
    const Zonotope<double> RA = Z.reduceAndAbsorb(part);
    check("reduceAndAbsorb count", RA.numGenerators() == q + n);
    check("reduceAndAbsorb encl.", contains(RA.interval(), p));

    // The lemmas behind both, again read off the blocks they produced. Column
    // q + i of each is the generator standing in for coordinate i.
    bool dropOk = true, mergeOk = true, keptOk = true;
    for (std::size_t i = 0; i < n; ++i) {
      double dropped = 0.0;
      for (std::size_t l = 0; l < part.right.size(); ++l)
        dropped += Z.G(i, part.right[l]) * beta[part.right[l]];
      dropOk = dropOk && std::fabs(dropped) <= R.G(i, q + i);

      const double mid = (Z.E.inf[i] + Z.E.sup[i]) / 2.0;
      mergeOk = mergeOk && std::fabs(dropped + (e[i] - mid)) <= RA.G(i, q + i);

      // The kept generators are copied, not recomputed.
      for (std::size_t l = 0; l < q; ++l)
        keptOk = keptOk && R.G(i, l) == Z.G(i, part.left[l]);
    }
    check("radius covers dropped", dropOk);
    check("merged block covers both", mergeOk);
    check("kept generators exact", keptOk);
  }

  // isValid is what stands in for Lean's equivalence, so it has to reject the
  // two ways a caller gets a partition wrong.
  check("rejects overlap", !Split{{0, 1}, {1, 2}}.isValid(3));
  check("rejects missing", !Split{{0}, {1}}.isValid(3));
  check("rejects out of range", !Split{{0, 3}, {1, 2}}.isValid(3));
  check("accepts partition", Split{{0, 2}, {1}}.isValid(3));
  check("accepts empty left", Split{{}, {0, 1, 2}}.isValid(3));

  return report("zonotope");
}
