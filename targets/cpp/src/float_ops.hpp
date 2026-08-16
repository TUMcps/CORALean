// Floating-point operations, and the ones derived from them.
//
// Specification: lean/src/CORALean/Arithmetic/Float/FloatOps.lean
//
// `FloatOps<F>` is the C++ form of the Lean class: specialize it for a scalar
// type and every algorithm below works over it. What makes those directions
// honest is `SoundFloatArithmetic`, which is proof-only and has no counterpart
// here.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <concepts>
#include <cstddef>

#include "tensor.hpp"

namespace cora {

/// Specialize per scalar type; see binary64.hpp.
template <class F>
struct FloatOps;

template <class F>
concept FloatScalar = requires(F a, F b) {
  { FloatOps<F>::zero() } -> std::same_as<F>;
  { FloatOps<F>::neg(a) } -> std::same_as<F>;
  { FloatOps<F>::addUp(a, b) } -> std::same_as<F>;
  { FloatOps<F>::addDown(a, b) } -> std::same_as<F>;
  { FloatOps<F>::mulUp(a, b) } -> std::same_as<F>;
  { FloatOps<F>::mulDown(a, b) } -> std::same_as<F>;
  { FloatOps<F>::minimum(a, b) } -> std::same_as<F>;
  { FloatOps<F>::maximum(a, b) } -> std::same_as<F>;
  { FloatOps<F>::half(a) } -> std::same_as<F>;
};

// Subtraction: negation is exact, so a directed difference is a directed sum.

template <FloatScalar F>
F subUp(F a, F b) {
  return FloatOps<F>::addUp(a, FloatOps<F>::neg(b));
}

template <FloatScalar F>
F subDown(F a, F b) {
  return FloatOps<F>::addDown(a, FloatOps<F>::neg(b));
}

// Summation. `addUp` is not associative, so the bracketing is part of the
// definition: right-nested, matching the Lean recursion on `Fin n`. Folding the
// other way would compute a different float and break agreement with `../c`.

template <FloatScalar F, class Fn>
F sumUp(std::size_t n, Fn f) {
  F acc = FloatOps<F>::zero();
  for (std::size_t i = n; i-- > 0;) acc = FloatOps<F>::addUp(f(i), acc);
  return acc;
}

template <FloatScalar F, class Fn>
F sumDown(std::size_t n, Fn f) {
  F acc = FloatOps<F>::zero();
  for (std::size_t i = n; i-- > 0;) acc = FloatOps<F>::addDown(f(i), acc);
  return acc;
}

/// Exact. Named as in Lean, where `abs` would have clashed with `|·|`.
template <FloatScalar F>
F absolute(F a) {
  return FloatOps<F>::maximum(a, FloatOps<F>::neg(a));
}

// Dot products: the products and the sum round the same way.

template <FloatScalar F, class RowA, class RowB>
F dotDown(std::size_t n, RowA a, RowB b) {
  return sumDown<F>(n, [&](std::size_t k) { return FloatOps<F>::mulDown(a(k), b(k)); });
}

template <FloatScalar F, class RowA, class RowB>
F dotUp(std::size_t n, RowA a, RowB b) {
  return sumUp<F>(n, [&](std::size_t k) { return FloatOps<F>::mulUp(a(k), b(k)); });
}

/// Row sums of absolute values, rounded up. Every use of it is a bound.
template <FloatScalar F>
Vec<F> radius(const Mat<F>& G) {
  Vec<F> r(G.rows());
  for (std::size_t i = 0; i < G.rows(); ++i)
    r[i] = sumUp<F>(G.cols(), [&](std::size_t j) { return absolute<F>(G(i, j)); });
  return r;
}

}  // namespace cora
