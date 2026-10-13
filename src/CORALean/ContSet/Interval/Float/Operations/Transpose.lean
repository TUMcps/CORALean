module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.transpose`

Transposing both bound matrices moves floats without computing on them, so nothing is rounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.transpose (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 n m) where
  inf := I.inf.transpose
  sup := I.sup.transpose

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
