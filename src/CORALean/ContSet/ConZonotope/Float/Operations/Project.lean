import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.project` over a floating-point scalar

The centre and every generator row at the chosen coordinates, the constraint polytope untouched
(it constrains the factors, not the coordinates), and the error box projected with
`Interval.project`. Selecting coordinates does no arithmetic, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.project (cZ : ConZonotope 𝕋 n) (dims : Fin m → Fin n) : ConZonotope 𝕋 m where
  h := cZ.h
  c := fun k => cZ.c (dims k)
  G := fun j k => cZ.G j (dims k)
  P := cZ.P
  E := cZ.E.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
