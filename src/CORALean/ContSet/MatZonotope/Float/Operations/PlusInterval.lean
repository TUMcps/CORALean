import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.MatZonotope.Float.MatZonotope

/-!
# `MatZonotope.plusInterval`

An interval matrix added to a matrix zonotope goes straight into the box, which is an
interval matrix already: the nominal part is untouched and only the box's bounds round.
How the exponential's remainder joins its Taylor sum.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatZonotope.plusInterval (Z : MatZonotope 𝕋 m n) (I : Interval (Mat 𝕋 m n)) :
    MatZonotope 𝕋 m n :=
  { Z with E := Interval.matPlus Z.E I }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
