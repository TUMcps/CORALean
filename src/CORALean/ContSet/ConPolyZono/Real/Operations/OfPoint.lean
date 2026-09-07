import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.ofPoint`

CORA's `conPolyZono` at a centre, no generators of either block and no
constraints: a single point, as the representation. What `OfPoint` asks every
representation with a point operation to supply.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


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
