import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.agreeMat`

The rows pinning the two points together, one per coordinate: the one
constraint `intersection` adds that reads both generator blocks at once.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows pinning the two points together, one per coordinate. -/
def ConZonotope.agreeMat (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) : Mat ℝ n (cZ₁.h + cZ₂.h) :=
  fun i => Fin.append (fun j => cZ₁.G j i) fun j => -cZ₂.G j i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
