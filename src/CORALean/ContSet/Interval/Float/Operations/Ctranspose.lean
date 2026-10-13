import CORALean.ContSet.Interval.Float.Operations.Transpose

/-!
# `Interval.ctranspose`

The conjugate transpose is the transpose over the reals a float reads as, so it moves floats only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ctranspose (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 n m) := I.transpose

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
