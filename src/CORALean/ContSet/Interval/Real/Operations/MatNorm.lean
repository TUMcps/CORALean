module

public import CORALean.ContSet.Interval.Real.Operations.NormTypeEval
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.matNorm`

CORA's `@intervalMatrix/norm`: for the types it supports, the matrix attaining the maximum norm
is `A_max = |center| + rad` (entrywise), and the answer is `norm(A_max, type)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `norm(intMat, type)`: the norm of `|center| + rad`. -/
noncomputable def Interval.matNorm (p : Interval.NormType) (A : Interval (Mat ℝ m n)) : ℝ :=
  let Amax : Mat ℝ m n := fun i j => |A.center i j| + A.radius i j
  p.eval Amax

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
