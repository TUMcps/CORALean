import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE

/-!
# The monomial read against the widened exponent matrix

Split out of `QuadMap.lean` (issue #62): read by `Theorems/SumExtEqPoint.lean`,
`Theorems/QuadEvalSumExt.lean` and `Theorems/MulPoint.lean`, all outside this
file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.extM (S : PolyZonotope α) (a : Fin S.p → ℝ) : Fin (S.h + 1) → ℝ :=
  PolyZonotope.monomial (PolyZonotope.extE S) a

end CORALean.Real
