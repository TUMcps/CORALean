import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.fullspace`, over a floating-point scalar

No constraints, so every point qualifies: what a zonotope's coefficients
answer to beyond the unit box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- No constraints, so every point qualifies: what a zonotope's coefficients
answer to beyond the unit box. -/
def HPolytope.fullspace (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 n where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float
