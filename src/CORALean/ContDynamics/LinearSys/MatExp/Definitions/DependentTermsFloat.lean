module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.DependentTerms`: the two outputs of `dependentTerms`, over a floating-point scalar

CORA's `[intSq, intH] = dependentTerms(obj, r)` with float interval matrices: the exact square
scaled by `r²`, and the exact Taylor terms of orders zero to two of the exponential.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The pair `[intSq, intH]` that `dependentTerms` returns. -/
structure MatExp.DependentTerms (𝕋 : Type) (n : ℕ) where
  /-- `r² A²`, the exact square scaled by the squared time step. -/
  intSq : Interval (Mat 𝕋 n n)
  /-- `I + A r + ½ A² r²`. -/
  intH : Interval (Mat 𝕋 n n)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
