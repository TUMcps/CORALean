// Splitting generator indices into a kept part and a dropped part.
//
// Specification: lean/CORALean/Global/Partition.lean
//
// Lean's `Split` is an equivalence, so "names every index exactly once" holds by
// construction. Here it is a run-time invariant that `isValid` checks, and the
// soundness proof of `reduce` genuinely depends on it: overlapping or missing
// indices would drop a generator from the result without accounting for it.
//
// Only `left` and `right` are ever used computationally, which is why this is
// two index vectors rather than a bijection.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#pragma once

#include <cstddef>
#include <vector>

namespace cora {

struct Split {
  std::vector<std::size_t> left;   ///< generators kept as they are
  std::vector<std::size_t> right;  ///< generators absorbed into a diagonal block

  /// True when the two parts together name each of `0..h-1` exactly once.
  bool isValid(std::size_t h) const {
    if (left.size() + right.size() != h) return false;
    std::vector<bool> seen(h, false);
    for (const auto* part : {&left, &right})
      for (std::size_t j : *part) {
        if (j >= h || seen[j]) return false;
        seen[j] = true;
      }
    return true;
  }
};

}  // namespace cora
