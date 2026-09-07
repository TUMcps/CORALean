import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.intersectionAgree`

The agreement rows' right-hand interval, and the only thing `intersection` computes:
the difference of the two centres, widened by how far the two error boxes let
the nominal points stand apart, each end rounded outward.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The agreement rows' right-hand interval, and the only thing `intersection` computes:
the difference of the two centres, widened by how far the two error boxes let
the nominal points stand apart, each end rounded outward. -/
def ConPolyZono.intersectionAgree (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => addDown (subDown (cPZ₂.c i) (cPZ₁.c i)) (subDown (cPZ₂.err.inf i) (cPZ₁.err.sup i)),
   fun i => addUp (subUp (cPZ₂.c i) (cPZ₁.c i)) (subUp (cPZ₂.err.sup i) (cPZ₁.err.inf i))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
