module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.ofPoint`

CORA's `polyZonotope` at a centre and no generators of either block: a single
point, as the representation. What `OfPoint` asks every representation with a
point operation to supply — `PolyZonotope.point` runs the other way, reading a
factor vector off an existing set, so it cannot stand in for this.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a polynomial zonotope with no dependent and no
independent generators. -/
def PolyZonotope.ofPoint (v : α) : PolyZonotope α := ⟨0, 0, 0, v, Fin.elim0, Fin.elim0, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
