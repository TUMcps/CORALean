module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.diagVec` over floats

A rearrangement: the diagonal of a matrix box is read off, so nothing is rounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.diagVec (I : Interval (Mat 𝕋 n n)) : Interval (Vec 𝕋 n) where
  inf := fun i => I.inf i i
  sup := fun i => I.sup i i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
