// Array types.
//
// Specification: lean/src/CORALean/Global/Tensor.lean
//
// Lean carries the dimensions in the type (`Mat F n h`); here they are fields,
// because `h` changes with every operation and C++ would need the sizes at
// compile time. Sizes are therefore checked at run time, not by the compiler.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cassert>
#include <cstddef>
#include <vector>

namespace cora {

template <class F>
using Vec = std::vector<F>;

/// Row-major, indexed `M(i, j)` to read like the Lean `G i j`.
template <class F>
class Mat {
 public:
  Mat() = default;

  Mat(std::size_t rows, std::size_t cols, F fill = F())
      : rows_(rows), cols_(cols), data_(rows * cols, fill) {}

  std::size_t rows() const { return rows_; }
  std::size_t cols() const { return cols_; }

  F& operator()(std::size_t i, std::size_t j) {
    assert(i < rows_ && j < cols_);
    return data_[i * cols_ + j];
  }

  const F& operator()(std::size_t i, std::size_t j) const {
    assert(i < rows_ && j < cols_);
    return data_[i * cols_ + j];
  }

 private:
  std::size_t rows_ = 0;
  std::size_t cols_ = 0;
  std::vector<F> data_;
};

}  // namespace cora
