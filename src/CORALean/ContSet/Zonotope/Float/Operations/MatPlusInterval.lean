import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.matPlusInterval`

An interval matrix added to a matrix zonotope goes straight into the box, which is an
interval matrix already: the nominal part is untouched and only the box's bounds round.
How the exponential's remainder joins its Taylor sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.matPlusInterval (Z : Zonotope (Mat 𝕋 m n)) (I : Interval (Mat 𝕋 m n)) :
    Zonotope (Mat 𝕋 m n) :=
  { Z with E := Interval.matPlus Z.E I }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
