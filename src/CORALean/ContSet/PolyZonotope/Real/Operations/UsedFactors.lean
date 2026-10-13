import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The factors some column still reads

Split out of `Compact.lean` (issue #62): used again by `Theorems/
CompactFactorsExact.lean`, and reused unchanged by `ConPolyZono.usedFactors`
over the joint exponent matrix, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors some column still reads. -/
def PolyZonotope.usedFactors {p h : ℕ} (E : Fin p → Fin h → ℕ) : Finset (Fin p) :=
  Finset.univ.filter fun k => ∃ i, E k i ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
