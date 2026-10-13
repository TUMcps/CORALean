module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Alg. 1` lines 6 and 9: the ratio test, cross-multiplied

`maxᵢ r_{s,i}/r_{sel,i} > µ̄`, cross-multiplied so that `r_sel = 0` reads as
line 4's `µ ← inf` rather than dividing by zero — the test `enclRatioLoop`
drives, its own file since [1, Alg. 1] names it at two separate lines.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6 and 9 together: `maxᵢ r_{s,i}/r_{sel,i} > µ̄`, cross-multiplied so
that `r_sel = 0` reads as line 4's `µ ← inf` rather than dividing by zero. -/
def Zonotope.ratioExceeds (lt : ℝ → ℝ → Bool) (rs rsel : Vec ℝ n) (μbar : ℝ) : Bool :=
  (List.finRange n).any fun j => lt (μbar * rsel j) (rs j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
