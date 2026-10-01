import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem

/-!
# `PolyZonotope.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: no generator of either kind leaves nothing to add to
the centre.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_ofPoint_iff (v x : α) :
    x ∈ (PolyZonotope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, _, _, h⟩
    simpa [PolyZonotope.ofPoint] using h
  · rintro rfl
    exact PolyZonotope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
