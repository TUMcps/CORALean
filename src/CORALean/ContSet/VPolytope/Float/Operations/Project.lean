module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.project` over a floating-point scalar

Every vertex read at the chosen coordinates, and the error box projected with
`Interval.project`. Selecting coordinates does no arithmetic, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.project (P : VPolytope (Vec 𝕋 n)) (dims : Fin m → Fin n) : VPolytope (Vec 𝕋 m) where
  k := P.k
  V := fun l i => P.V l (dims i)
  I_error := P.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
