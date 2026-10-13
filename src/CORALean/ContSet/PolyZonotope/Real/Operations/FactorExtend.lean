import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors
import Mathlib.Data.Finset.Sort

/-!
# A kept-factor vector, read back over every factor

Split out of `Compact.lean` (issue #62): used again by `Theorems/
CompactFactorsExact.lean`, and reused unchanged by `ConPolyZono.factorExtend`,
both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A factor vector over the kept factors, read back over all of them by giving
a dropped factor the value zero — admissible, and read by no monomial. -/
def PolyZonotope.factorExtend {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ) (k : Fin p) : ℝ :=
  if hk : k ∈ PolyZonotope.usedFactors E then
    a (((PolyZonotope.usedFactors E).orderIsoOfFin rfl).symm ⟨k, hk⟩)
  else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
