module

public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.Point

@[expose] public section

/-!
# `VPolytope.mpower`

CORA's `@matPolytope/mpower`: the zero power is the identity (a single vertex), the first is the
polytope itself, and from the second on `matP * matP` is multiplied by `matP` on the right, once per
further exponent. Only for square matrices.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `matP ^ k` of CORA, left to right: `((P * P) * P) * …`. -/
def VPolytope.mpower (P : VPolytope (Mat ℝ n n)) : ℕ → VPolytope (Mat ℝ n n)
  | 0 => VPolytope.point 1
  | 1 => P
  | k + 2 => VPolytope.matMul (VPolytope.mpower P (k + 1)) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
