import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.project` over a floating-point scalar

Every vertex read at the chosen coordinates, and the error box projected with
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

def VPolytope.project (P : VPolytope (Vec 𝕋 n)) (dims : Fin m → Fin n) : VPolytope (Vec 𝕋 m) where
  k := P.k
  V := fun l i => P.V l (dims i)
  E := P.E.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
