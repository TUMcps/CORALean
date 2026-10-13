import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.project` over a floating-point scalar

The centre and every generator row at the chosen coordinates, and the error box projected with
`Interval.project`. Selecting coordinates moves stored floats without arithmetic, so nothing
rounds and the generator count is unchanged. `dims` may repeat or reorder coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.project (Z : Zonotope (Vec 𝕋 n)) (dims : Fin m → Fin n) : Zonotope (Vec 𝕋 m) where
  h := Z.h
  c := fun k => Z.c (dims k)
  G := fun j k => Z.G j (dims k)
  E := Z.E.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
