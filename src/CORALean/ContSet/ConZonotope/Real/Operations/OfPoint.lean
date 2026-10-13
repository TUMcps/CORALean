import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

/-!
# `ConZonotope.ofPoint`

CORA's `conZonotope` at a centre, no generators and no constraints: a single
point, as the representation. What `OfPoint` asks every representation with a
point operation to supply.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a constrained zonotope with no generators and no
constraints. -/
def ConZonotope.ofPoint (v : α) : ConZonotope α := ⟨0, v, Fin.elim0, HPolytope.fullspace _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
