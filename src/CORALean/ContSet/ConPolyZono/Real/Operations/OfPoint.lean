module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.ofPoint`

CORA's `conPolyZono` at a center, no generators of either block and no
constraints: a single point, as the representation. What `OfPoint` asks every
representation with a point operation to supply.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a constrained polynomial zonotope with no generators
and an empty constraint system. -/
def ConPolyZono.ofPoint (v : α) : ConPolyZono α :=
  ⟨0, 0, 0, 0, 0, v, Fin.elim0, Fin.elim0, Fin.elim0, 0, ⟨0, 0⟩, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
