import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE

/-!
# The monomial read against the widened exponent matrix

Split out of `QuadMap.lean` (issue #62): read by `Theorems/SumExtEqPoint.lean`,
`Theorems/QuadEvalSumExt.lean` and `Theorems/MulPoint.lean`, all outside this
file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.extM (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : Fin (pZ.h + 1) → ℝ :=
  PolyZonotope.monomial (PolyZonotope.extE pZ) a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
