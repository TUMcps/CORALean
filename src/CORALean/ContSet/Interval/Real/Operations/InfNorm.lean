module

public import CORALean.ContSet.Interval.Real.Operations.NormTypeEval
public import CORALean.ContSet.Interval.Real.Operations.AbsMax

@[expose] public section

/-!
# `Interval.infNorm`

CORA's `@intervalMatrix/infNorm`: `norm(abs(A), Inf)`, the maximum absolute row sum of the matrix
`abs(A)` (`absMax`) that dominates every member.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `infNorm(A) = norm(abs(A), Inf)`. -/
noncomputable def Interval.infNorm (A : Interval (Mat ℝ m n)) : ℝ :=
  Interval.NormType.eval .inf A.absMax

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
