import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.horzcat` over floats

Concatenating the bound matrices side by side moves floats without computing on them, so
nothing is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.horzcat (I : Interval (Mat 𝕋 m n₁)) (J : Interval (Mat 𝕋 m n₂)) :
    Interval (Mat 𝕋 m (n₁ + n₂)) where
  inf := fun i => Fin.append (I.inf i) (J.inf i)
  sup := fun i => Fin.append (I.sup i) (J.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
