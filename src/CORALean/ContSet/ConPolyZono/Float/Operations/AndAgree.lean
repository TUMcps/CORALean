import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.andAgree`

The agreement rows' right-hand interval, and the only thing `and` computes:
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

/-- The agreement rows' right-hand interval, and the only thing `and` computes:
the difference of the two centres, widened by how far the two error boxes let
the nominal points stand apart, each end rounded outward. -/
def ConPolyZono.andAgree (C₁ C₂ : ConPolyZono 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => addDown (subDown (C₂.c i) (C₁.c i)) (subDown (C₂.err.inf i) (C₁.err.sup i)),
   fun i => addUp (subUp (C₂.c i) (C₁.c i)) (subUp (C₂.err.sup i) (C₁.err.inf i))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
