// Zonotopes over a floating-point scalar.
//
// Specification: lean/src/CORALean/Arithmetic/Float/ContSet/Zonotope/API.lean
//
// CORA's `zonotope` with its centre and generator matrix, plus the error box
// that makes it an `InflatedContSet`. The nominal part is the zonotope the
// stored floats describe; the box holds what rounding has cost.
//
// `InflatedContSet` itself has no counterpart here: `nominal` and `construct`
// are denotations, which do not run. What survives is the field `E` and the
// discipline of paying every rounding into it.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cassert>
#include <cstddef>

#include "float_ops.hpp"
#include "interval.hpp"
#include "partition.hpp"
#include "tensor.hpp"

namespace cora {

/// One generator per coordinate, `v` on the diagonal.
template <FloatScalar F>
Mat<F> diagonalBlock(const Vec<F>& v) {
  Mat<F> D(v.size(), v.size(), FloatOps<F>::zero());
  for (std::size_t i = 0; i < v.size(); ++i) D(i, i) = v[i];
  return D;
}

// Rounded linear algebra. Each entry is a dot product; both directions are kept,
// the stored value being the lower one and the gap to the upper what the box is
// charged.

template <FloatScalar F>
Vec<F> mulVecDown(const Mat<F>& M, const Vec<F>& v) {
  assert(M.cols() == v.size());
  Vec<F> r(M.rows());
  for (std::size_t i = 0; i < M.rows(); ++i)
    r[i] = dotDown<F>(M.cols(), [&](std::size_t k) { return M(i, k); },
                      [&](std::size_t k) { return v[k]; });
  return r;
}

template <FloatScalar F>
Vec<F> mulVecUp(const Mat<F>& M, const Vec<F>& v) {
  assert(M.cols() == v.size());
  Vec<F> r(M.rows());
  for (std::size_t i = 0; i < M.rows(); ++i)
    r[i] = dotUp<F>(M.cols(), [&](std::size_t k) { return M(i, k); },
                    [&](std::size_t k) { return v[k]; });
  return r;
}

template <FloatScalar F>
Mat<F> matMulDown(const Mat<F>& M, const Mat<F>& G) {
  assert(M.cols() == G.rows());
  Mat<F> R(M.rows(), G.cols());
  for (std::size_t i = 0; i < M.rows(); ++i)
    for (std::size_t j = 0; j < G.cols(); ++j)
      R(i, j) = dotDown<F>(M.cols(), [&](std::size_t k) { return M(i, k); },
                           [&](std::size_t k) { return G(k, j); });
  return R;
}

template <FloatScalar F>
Mat<F> matMulUp(const Mat<F>& M, const Mat<F>& G) {
  assert(M.cols() == G.rows());
  Mat<F> R(M.rows(), G.cols());
  for (std::size_t i = 0; i < M.rows(); ++i)
    for (std::size_t j = 0; j < G.cols(); ++j)
      R(i, j) = dotUp<F>(M.cols(), [&](std::size_t k) { return M(i, k); },
                         [&](std::size_t k) { return G(k, j); });
  return R;
}

/// How far a stored generator entry can be from the exact product.
template <FloatScalar F>
Mat<F> matMulDiff(const Mat<F>& M, const Mat<F>& G) {
  const Mat<F> up = matMulUp<F>(M, G);
  const Mat<F> down = matMulDown<F>(M, G);
  Mat<F> R(up.rows(), up.cols());
  for (std::size_t i = 0; i < up.rows(); ++i)
    for (std::size_t j = 0; j < up.cols(); ++j) R(i, j) = subUp<F>(up(i, j), down(i, j));
  return R;
}

template <FloatScalar F>
struct Zonotope {
  Vec<F> c;      ///< centre, dimension n
  Mat<F> G;      ///< generators, n by h
  Interval<F> E; ///< what rounding has cost, dimension n

  std::size_t dim() const { return c.size(); }
  std::size_t numGenerators() const { return G.cols(); }

  /// What generators known only to within `G` entrywise cost: coefficients
  /// range over `[-1, 1]`, so a row sums with no cancellation.
  static Interval<F> generatorError(const Mat<F>& G) {
    return Interval<F>::symmetric(radius<F>(G));
  }

  /// Storing the lower of the two directed roundings leaves this much to pay.
  static Interval<F> centerResidual(const Vec<F>& a, const Vec<F>& b) {
    assert(a.size() == b.size());
    Vec<F> lo(a.size()), hi(a.size());
    for (std::size_t i = 0; i < a.size(); ++i) {
      lo[i] = FloatOps<F>::addDown(a[i], b[i]);
      hi[i] = FloatOps<F>::addUp(a[i], b[i]);
    }
    return Interval<F>::residual(lo, hi, lo);
  }

  /// The box midpoint added to the centre, rounded each way. The exact midpoint
  /// need not be a float — `[5, 6]` gives 5.5 — so the gap between the two
  /// roundings is what `absorbError` leaves behind.
  Vec<F> shiftDown() const {
    Vec<F> s(dim());
    for (std::size_t i = 0; i < dim(); ++i)
      s[i] = FloatOps<F>::addDown(c[i], FloatOps<F>::half(FloatOps<F>::addDown(E.inf[i], E.sup[i])));
    return s;
  }

  Vec<F> shiftUp() const {
    Vec<F> s(dim());
    for (std::size_t i = 0; i < dim(); ++i)
      s[i] = FloatOps<F>::addUp(c[i], FloatOps<F>::half(FloatOps<F>::addUp(E.inf[i], E.sup[i])));
    return s;
  }

  /// The box radius, rounded up; halving is exact, so only the difference rounds.
  Vec<F> errorRadius() const {
    Vec<F> r(dim());
    for (std::size_t i = 0; i < dim(); ++i)
      r[i] = FloatOps<F>::half(subUp<F>(E.sup[i], E.inf[i]));
    return r;
  }

  /// Trade the box for `n` generators about its own midpoint. Over ℝ this moves
  /// nothing; here the shifted centre must be stored as a float, so the box is
  /// left holding what that rounding still owes rather than becoming `[0, 0]`.
  Zonotope absorbError() const {
    const Vec<F> lo = shiftDown();
    const Vec<F> hi = shiftUp();
    Zonotope Z{lo, Mat<F>(dim(), numGenerators() + dim()),
               Interval<F>::residual(lo, hi, lo)};
    const Mat<F> D = diagonalBlock<F>(errorRadius());
    for (std::size_t i = 0; i < dim(); ++i) {
      for (std::size_t j = 0; j < numGenerators(); ++j) Z.G(i, j) = G(i, j);
      for (std::size_t l = 0; l < dim(); ++l) Z.G(i, numGenerators() + l) = D(i, l);
    }
    return Z;
  }

  /// CORA's `reduce`, unchanged in shape, and sound for every partition.
  ///
  /// Nothing is charged to the box: the centre and the kept generators are
  /// copied exactly, and the diagonal block rounds up, which only enlarges a
  /// result that was already an over-approximation.
  Zonotope reduce(const Split& part) const {
    assert(part.isValid(numGenerators()));
    const std::size_t q = part.left.size();
    Zonotope Z{c, Mat<F>(dim(), q + dim()), E};
    const Mat<F> D = diagonalBlock<F>(droppedRadius(part));
    for (std::size_t i = 0; i < dim(); ++i) {
      for (std::size_t l = 0; l < q; ++l) Z.G(i, l) = G(i, part.left[l]);
      for (std::size_t l = 0; l < dim(); ++l) Z.G(i, q + l) = D(i, l);
    }
    return Z;
  }

  /// `reduce` and `absorbError` in one pass, and the reason to prefer it.
  ///
  /// Each alone ends in a diagonal block, and two merge into one with summed
  /// radii, since per coordinate they are independent. Doing both therefore
  /// costs the `q + n` generators `reduce` alone would; run separately they cost
  /// `q + n + n`.
  Zonotope reduceAndAbsorb(const Split& part) const {
    assert(part.isValid(numGenerators()));
    const std::size_t q = part.left.size();
    const Vec<F> lo = shiftDown();
    const Vec<F> hi = shiftUp();
    const Vec<F> dropped = droppedRadius(part);
    const Vec<F> er = errorRadius();

    Vec<F> merged(dim());
    for (std::size_t i = 0; i < dim(); ++i) merged[i] = FloatOps<F>::addUp(dropped[i], er[i]);

    Zonotope Z{lo, Mat<F>(dim(), q + dim()), Interval<F>::residual(lo, hi, lo)};
    const Mat<F> D = diagonalBlock<F>(merged);
    for (std::size_t i = 0; i < dim(); ++i) {
      for (std::size_t l = 0; l < q; ++l) Z.G(i, l) = G(i, part.left[l]);
      for (std::size_t l = 0; l < dim(); ++l) Z.G(i, q + l) = D(i, l);
    }
    return Z;
  }

  /// CORA's `@zonotope/interval`: the hull `c ± radius G`, inflated by the box.
  /// An `Interval` has no box, so the bounds themselves absorb every rounding.
  Interval<F> interval() const {
    const Vec<F> r = radius<F>(G);
    Interval<F> I{Vec<F>(dim()), Vec<F>(dim())};
    for (std::size_t i = 0; i < dim(); ++i) {
      I.inf[i] = FloatOps<F>::addDown(subDown<F>(c[i], r[i]), E.inf[i]);
      I.sup[i] = FloatOps<F>::addUp(FloatOps<F>::addUp(c[i], r[i]), E.sup[i]);
    }
    return I;
  }

  /// What `mtimes` owes beyond its nominal part: the centre, and the generators.
  static Interval<F> mtimesResidual(const Mat<F>& M, const Zonotope& Z) {
    const Vec<F> lo = mulVecDown<F>(M, Z.c);
    const Vec<F> hi = mulVecUp<F>(M, Z.c);
    return Interval<F>::residual(lo, hi, lo).plus(generatorError(matMulDiff<F>(M, Z.G)));
  }

  /// The generator count is untouched, the rounding being paid into the box; the
  /// old box travels through the map as a box.
  static Zonotope mtimes(const Mat<F>& M, const Zonotope& Z) {
    assert(M.cols() == Z.dim());
    return Zonotope{mulVecDown<F>(M, Z.c), matMulDown<F>(M, Z.G),
                    Interval<F>::mtimes(M, Z.E).plus(mtimesResidual(M, Z))};
  }

  /// Generators concatenate exactly, so only the centre rounds and its residual
  /// goes into the box. The generator count is `h + k`, exactly as over ℝ.
  Zonotope plus(const Zonotope& other) const {
    assert(dim() == other.dim());
    const std::size_t h = numGenerators();
    const std::size_t k = other.numGenerators();

    Zonotope Z{Vec<F>(dim()), Mat<F>(dim(), h + k),
               E.plus(other.E).plus(centerResidual(c, other.c))};
    for (std::size_t i = 0; i < dim(); ++i) {
      Z.c[i] = FloatOps<F>::addDown(c[i], other.c[i]);
      for (std::size_t j = 0; j < h; ++j) Z.G(i, j) = G(i, j);
      for (std::size_t j = 0; j < k; ++j) Z.G(i, h + j) = other.G(i, j);
    }
    return Z;
  }

 private:
  /// Row sums of the generators the partition drops, rounded up.
  Vec<F> droppedRadius(const Split& part) const {
    Vec<F> r(dim());
    for (std::size_t i = 0; i < dim(); ++i)
      r[i] = sumUp<F>(part.right.size(),
                      [&](std::size_t l) { return absolute<F>(G(i, part.right[l])); });
    return r;
  }
};

}  // namespace cora
