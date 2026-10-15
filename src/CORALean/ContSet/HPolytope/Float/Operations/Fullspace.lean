module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.fullspace`, over a floating-point scalar

No constraints, so every point qualifies: what a zonotope's coefficients
answer to beyond the unit box.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No constraints, so every point qualifies: what a zonotope's coefficients
answer to beyond the unit box. -/
def HPolytope.fullspace (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := 0
  Ae := fun i => i.elim0
  be := fun i => i.elim0
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
