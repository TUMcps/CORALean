module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.vertcat` over floats

Stacking the bound matrices moves floats without computing on them, so nothing is rounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m₁ m₂ n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.vertcat (I : Interval (Mat 𝕋 m₁ n)) (J : Interval (Mat 𝕋 m₂ n)) :
    Interval (Mat 𝕋 (m₁ + m₂) n) where
  inf := Fin.append I.inf J.inf
  sup := Fin.append I.sup J.sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
