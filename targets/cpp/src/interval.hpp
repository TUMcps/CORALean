// Intervals over a floating-point scalar.
//
// Specification: lean/src/CORALean/Arithmetic/Float/ContSet/Interval/API.lean
//
// Each bound rounds away from the interval: `inf` down, `sup` up. That is the
// whole of the floating-point content.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cassert>
#include <cstddef>

#include "float_ops.hpp"
#include "tensor.hpp"

namespace cora {

template <FloatScalar F>
struct Interval {
  Vec<F> inf;
  Vec<F> sup;

  std::size_t dim() const { return inf.size(); }

  /// The box `[-r, r]`.
  static Interval symmetric(const Vec<F>& r) {
    Interval I{Vec<F>(r.size()), r};
    for (std::size_t i = 0; i < r.size(); ++i) I.inf[i] = FloatOps<F>::neg(r[i]);
    return I;
  }

  /// The intended vector is in `[lo, hi]` but `stored` was written down.
  static Interval residual(const Vec<F>& lo, const Vec<F>& hi, const Vec<F>& stored) {
    assert(lo.size() == hi.size() && hi.size() == stored.size());
    Interval I{Vec<F>(lo.size()), Vec<F>(lo.size())};
    for (std::size_t i = 0; i < lo.size(); ++i) {
      I.inf[i] = subDown<F>(lo[i], stored[i]);
      I.sup[i] = subUp<F>(hi[i], stored[i]);
    }
    return I;
  }

  Interval plus(const Interval& other) const {
    assert(dim() == other.dim());
    Interval I{Vec<F>(dim()), Vec<F>(dim())};
    for (std::size_t i = 0; i < dim(); ++i) {
      I.inf[i] = FloatOps<F>::addDown(inf[i], other.inf[i]);
      I.sup[i] = FloatOps<F>::addUp(sup[i], other.sup[i]);
    }
    return I;
  }

  /// `minimum`/`maximum` absorb the sign of `M(i, k)` as `min`/`max` do over ℝ.
  static Interval mtimes(const Mat<F>& M, const Interval& I) {
    assert(M.cols() == I.dim());
    Interval R{Vec<F>(M.rows()), Vec<F>(M.rows())};
    for (std::size_t i = 0; i < M.rows(); ++i) {
      R.inf[i] = sumDown<F>(M.cols(), [&](std::size_t k) {
        return FloatOps<F>::minimum(FloatOps<F>::mulDown(M(i, k), I.inf[k]),
                                    FloatOps<F>::mulDown(M(i, k), I.sup[k]));
      });
      R.sup[i] = sumUp<F>(M.cols(), [&](std::size_t k) {
        return FloatOps<F>::maximum(FloatOps<F>::mulUp(M(i, k), I.inf[k]),
                                    FloatOps<F>::mulUp(M(i, k), I.sup[k]));
      });
    }
    return R;
  }
};

}  // namespace cora
