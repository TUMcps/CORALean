import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.agreeMat`

The rows pinning the two points together, one per coordinate: the one
constraint `and` adds that reads both generator blocks at once.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows pinning the two points together, one per coordinate. -/
def ConZonotope.agreeMat (C₁ C₂ : ConZonotope (Vec ℝ n)) : Mat ℝ n (C₁.h + C₂.h) :=
  fun i => Fin.append (fun j => C₁.G j i) fun j => -C₂.G j i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
