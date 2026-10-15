module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `MatExp.DependentTerms`: the two outputs of `dependentTerms`

CORA's `[intSq, intH] = dependentTerms(obj, r)`: the exact square, scaled by `r²`, and the exact
Taylor terms of orders zero to two of the exponential, `I + A r + ½ A² r²`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- The pair `[intSq, intH]` that `dependentTerms` returns. -/
structure MatExp.DependentTerms (n : ℕ) where
  /-- `r² A²`, the exact square scaled by the squared time step. -/
  intSq : Interval (Mat ℝ n n)
  /-- `I + A r + ½ A² r²`. -/
  intH : Interval (Mat ℝ n n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
