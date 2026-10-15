module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# The result of `dependentTerms` at a matrix zonotope

The pair `[zSq, zH]` that CORA's `@matZonotope/dependentTerms` returns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The pair `[zSq, zH]` that `dependentTerms` returns at a matrix zonotope. -/
structure MatExp.DependentTermsMatZono (n : ℕ) where
  /-- `r² M²`, the square scaled by the squared time step. -/
  zSq : Zonotope (Mat ℝ n n)
  /-- `I + M r + ½ M² r²`. -/
  zH : Zonotope (Mat ℝ n n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
